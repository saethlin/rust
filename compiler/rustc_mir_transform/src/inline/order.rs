//! A well-founded order on the bodies whose MIR the inliner may request.
//!
//! Every `optimized_mir(X) -> optimized_mir(Z)` query edge is created by X's own inliner, at a
//! point where it knows exactly which body it is about to request. So instead of predicting
//! whether some other body would request X (which needs a complete and exact call graph), each
//! request is checked locally: X may only request optimized-MIR-derived facts of a local body Z
//! if `rank(Z) < rank(X)`. Any chain of such requests strictly descends, so it cannot cycle.
//! The call graph below only decides how much inlining the ranks allow, never soundness.
//!
//! Ranks are computed from tracked queries read before the guarded request, so if an edit
//! changes the order, red-green marking stops there before replaying a stale `optimized_mir`
//! read.
//!
//! The ranks:
//! - Upstream items (MIR from metadata) and constructors are unconstrained.
//! - Fixed tiers that never consult the crate-wide order, because coroutines are optimized
//!   during analysis (for their layout) and the order needs every body's MIR:
//!   - [`BOTTOM`]: shims that don't read local MIR.
//!   - [`LEAF`]: bodies that can't reach any local code.
//!   - [`COROUTINE`]: coroutines, which may therefore only request leaves. `coroutine_layout`
//!     reads `optimized_mir` without going through this guard, so a coroutine must never request
//!     a body that mentions it; leaves mention no local types at all.
//!   - Shims built from a coroutine's optimized MIR rank one above it.
//! - Every other body ranks by the height of its strongly connected component in an approximate
//!   call graph, above all fixed tiers. Members of one component share a rank, so recursion is
//!   never inlined into itself, and unrelated components of the same height are incomparable,
//!   so the order doesn't depend on names.

use rustc_attr_ir::{InlineAttr, OptimizeAttr};
use rustc_data_structures::fx::{FxHashSet, FxIndexMap, FxIndexSet};
use rustc_data_structures::graph::scc::Sccs;
use rustc_data_structures::graph::vec_graph::VecGraph;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::{Idx, IndexVec};
use rustc_middle::mir::TerminatorKind;
use rustc_middle::ty::{
    self, GenericArgs, Instance, InstanceKind, ShimKind, Ty, TyCtxt, TypeVisitableExt,
};
use rustc_session::Session;
use rustc_session::config::OptLevel;
use rustc_span::sym;
use tracing::{debug, instrument};

use crate::pass_manager::{self as pm, PassCtx};

const BOTTOM: usize = 0;
const LEAF: usize = 1;
const COROUTINE: usize = 2;

#[derive(Copy, Clone, Debug)]
enum Rank {
    /// Requesting this can never cycle.
    Unconstrained,
    /// Below every graph rank.
    Fixed(usize),
    /// `2 * height(body) + offset` above the fixed tiers, resolved only when two graph ranks meet.
    Graph { body: LocalDefId, offset: usize },
}

/// Whether some body of this session may consult the order. Must be a superset of "`Inline`
/// runs for some body, or `ForceInline` meets a local callee", and must not use queries that
/// could cycle back into MIR building, because it decides whether bodies are scanned before
/// their MIR is stolen.
pub(crate) fn order_may_be_used(tcx: TyCtxt<'_>) -> bool {
    // Local `#[rustc_force_inline]` functions need `rustc_attrs`.
    tcx.features().rustc_attrs() || inline_may_run(tcx.sess)
}

fn inline_may_run(sess: &Session) -> bool {
    // `#[optimize(speed)]` can raise a body's MIR opt level; other attributes only lower it.
    [sess.mir_opt_level(), OptLevel::Aggressive.mir_opt_level()]
        .into_iter()
        .any(|level| pm::should_run_pass(&super::Inline, &PassCtx::with_mir_opt_level(sess, level)))
}

/// The guard: may the body of `caller` request optimized-MIR-derived facts of `callee`?
#[instrument(level = "debug", skip(tcx), ret)]
pub(crate) fn may_request<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: InstanceKind<'tcx>,
    callee: InstanceKind<'tcx>,
) -> bool {
    let callee_rank = instance_rank(tcx, callee);
    if let Rank::Unconstrained = callee_rank {
        return true;
    }
    if !order_may_be_used(tcx) {
        // The bodies weren't scanned, so no rank is known. Refusing is always sound.
        return false;
    }
    let caller_rank = instance_rank(tcx, caller);
    debug!(?callee_rank, ?caller_rank);
    lt(tcx, callee_rank, caller_rank)
}

fn lt(tcx: TyCtxt<'_>, a: Rank, b: Rank) -> bool {
    match (a, b) {
        (_, Rank::Unconstrained) => false,
        (Rank::Unconstrained, _) => true,
        (Rank::Fixed(x), Rank::Fixed(y)) => x < y,
        (Rank::Fixed(_), Rank::Graph { .. }) => true,
        (Rank::Graph { .. }, Rank::Fixed(_)) => false,
        (Rank::Graph { body: a, offset: i }, Rank::Graph { body: b, offset: j }) => {
            let order = tcx.mir_inliner_order(());
            // A body missing from the order can't call anything; it ranks below every node.
            let base = |body| order.get(&body).map_or(0, |&height| 2 * (height + 1));
            base(a) + i < base(b) + j
        }
    }
}

fn above(rank: Rank) -> Rank {
    match rank {
        Rank::Unconstrained => Rank::Fixed(BOTTOM),
        Rank::Fixed(x) => Rank::Fixed(x + 1),
        Rank::Graph { body, offset } => Rank::Graph { body, offset: offset + 1 },
    }
}

fn instance_rank<'tcx>(tcx: TyCtxt<'tcx>, instance: InstanceKind<'tcx>) -> Rank {
    match instance {
        InstanceKind::Item(def_id) | InstanceKind::Intrinsic(def_id) => match def_id.as_local() {
            Some(def_id) => body_rank(tcx, def_id),
            None => Rank::Unconstrained,
        },
        InstanceKind::Shim(shim) => shim_rank(tcx, shim),
        // These have no MIR of their own.
        InstanceKind::LlvmIntrinsic(_) | InstanceKind::Virtual(..) => Rank::Unconstrained,
    }
}

fn body_rank(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Rank {
    if tcx.is_constructor(def_id.to_def_id()) {
        // Constructor MIR is built directly and never runs the inliner.
        Rank::Unconstrained
    } else if !is_graph_candidate(tcx, def_id) {
        Rank::Fixed(COROUTINE)
    } else if is_leaf(tcx, def_id) {
        Rank::Fixed(LEAF)
    } else {
        Rank::Graph { body: def_id, offset: 0 }
    }
}

/// Shims rank one above every local body whose optimized MIR they read while being built, or
/// that their `ForceInline` pass may inline.
fn shim_rank<'tcx>(tcx: TyCtxt<'tcx>, shim: ShimKind<'tcx>) -> Rank {
    let mut deps: Vec<LocalDefId> = Vec::new();
    let tys: &[Ty<'tcx>] = match &shim {
        ShimKind::FnPtr(_, ty)
        | ShimKind::Clone(_, ty)
        | ShimKind::FnPtrAsPtr(_, ty)
        | ShimKind::FnPtrFromPtr(_, ty)
        | ShimKind::AsyncDropGlue(_, ty)
        | ShimKind::AsyncDropGlueCtor(_, ty) => std::slice::from_ref(ty),
        ShimKind::DropGlue(_, ty) => ty.as_slice(),
        ShimKind::FutureDropPoll(_, proxy_ty, impl_ty) => &[*proxy_ty, *impl_ty],
        ShimKind::VTable(_)
        | ShimKind::Reify(..)
        | ShimKind::ClosureOnce { .. }
        | ShimKind::ConstructCoroutineInClosure { .. }
        | ShimKind::ThreadLocal(_) => &[],
    };
    // Drop glue and async drop shims of coroutines are built from the coroutine's optimized MIR.
    if let ShimKind::DropGlue(..)
    | ShimKind::FutureDropPoll(..)
    | ShimKind::AsyncDropGlue(..)
    | ShimKind::AsyncDropGlueCtor(..) = shim
    {
        deps.extend(tys.iter().filter_map(|ty| match *ty.kind() {
            ty::Coroutine(def_id, _) => def_id.as_local(),
            _ => None,
        }));
    }
    // Async drop shims start from the optimized MIR of `async_drop_in_place`.
    if let ShimKind::AsyncDropGlue(def_id, _) | ShimKind::AsyncDropGlueCtor(def_id, _) = shim {
        deps.extend(def_id.as_local());
    }
    // Shims call the function they wrap, which their `ForceInline` pass inlines if required.
    let def_id = InstanceKind::Shim(shim).def_id();
    if let Some(local) = def_id.as_local()
        && is_force_inline(tcx, def_id)
    {
        deps.push(local);
    }
    for &ty in tys {
        for arg in ty.walk() {
            if let Some(ty) = arg.as_type()
                && let ty::FnDef(def_id, _) = *ty.kind()
                && let Some(local) = def_id.as_local()
                && is_force_inline(tcx, def_id)
            {
                deps.push(local);
            }
        }
    }

    deps.into_iter()
        .map(|dep| body_rank(tcx, dep))
        .reduce(|a, b| if lt(tcx, a, b) { b } else { a })
        .map_or(Rank::Fixed(BOTTOM), above)
}

/// Local bodies that may rank by the call graph. Coroutines rank in a fixed tier instead.
fn is_graph_candidate(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    match tcx.def_kind(def_id) {
        DefKind::Fn | DefKind::AssocFn => true,
        DefKind::Closure => !tcx.is_coroutine(def_id.to_def_id()),
        _ => false,
    }
}

/// Whether `ty` contains a local item: a function or closure a body could call, or any local type,
/// which disqualifies a body from being a leaf (coroutines and opaque types because of their
/// layout, ADTs because trait methods may resolve to local impls for them).
fn mentions_local<'tcx>(ty: Ty<'tcx>) -> bool {
    ty.walk().filter_map(|arg| arg.as_type()).any(|ty| {
        let def_id = match *ty.kind() {
            ty::Adt(adt, _) => adt.did(),
            ty::FnDef(def_id, _)
            | ty::Closure(def_id, _)
            | ty::CoroutineClosure(def_id, _)
            | ty::Coroutine(def_id, _)
            | ty::Foreign(def_id) => def_id,
            ty::Alias(_, ty::AliasTy { kind: ty::Opaque { def_id }, .. }) => def_id,
            _ => return false,
        };
        def_id.is_local()
    })
}

fn args_mention_local<'tcx>(args: GenericArgs<'tcx>) -> bool {
    args.iter().filter_map(|arg| arg.as_type()).any(mentions_local)
}

pub(crate) fn mir_inliner_callees<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceKind<'tcx>,
) -> (&'tcx [(DefId, GenericArgs<'tcx>)], &'tcx [Ty<'tcx>]) {
    let steal;
    let guard;
    let body = match (instance, instance.def_id().as_local()) {
        (InstanceKind::Item(_), Some(def_id)) => {
            steal = tcx.mir_promoted(def_id).0;
            guard = steal.borrow();
            &*guard
        }
        // Functions from other crates and MIR shims
        _ => tcx.instance_mir(instance),
    };
    let mut calls = FxIndexSet::default();
    for bb_data in body.basic_blocks.iter() {
        let terminator = bb_data.terminator();
        if let TerminatorKind::Call { func, args: call_args, .. } = &terminator.kind {
            let ty = func.ty(&body.local_decls, tcx);
            let ty::FnDef(def_id, generic_args) = ty.kind() else {
                continue;
            };
            let call = if tcx.is_intrinsic(*def_id, sym::const_eval_select) {
                let func = &call_args[2].node;
                let ty = func.ty(&body.local_decls, tcx);
                let ty::FnDef(def_id, generic_args) = ty.kind() else {
                    continue;
                };
                (*def_id, *generic_args)
            } else {
                (*def_id, *generic_args)
            };
            calls.insert(call);
        }
    }
    let calls = tcx
        .arena
        .alloc_from_iter(calls.iter().map(|(did, args)| (*did, args.no_bound_vars().unwrap())));
    // Only `#[rustc_force_inline]` functions can be leaves, which mention no local item (see
    // `is_leaf`). One local type is enough to tell.
    let mentions: &[Ty<'tcx>] = match instance {
        InstanceKind::Item(def_id) if def_id.is_local() && is_force_inline(tcx, def_id) => {
            tcx.arena.alloc_from_iter(
                body.local_decls.iter().map(|decl| decl.ty).find(|&ty| mentions_local(ty)),
            )
        }
        _ => &[],
    };
    (calls, mentions)
}

fn is_force_inline(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    // Local `#[rustc_force_inline]` functions need `rustc_attrs`, see `order_may_be_used`.
    (!def_id.is_local() || tcx.features().rustc_attrs())
        && matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
        && matches!(tcx.codegen_fn_attrs(def_id).inline, InlineAttr::Force { .. })
}

/// A leaf calls only upstream functions, with upstream types, and mentions no local item. So
/// everything its inliner can reach is upstream, and its optimized MIR can't depend on the
/// layout of a local coroutine. Only coroutines and shims need leaves, and their `ForceInline`
/// pass only inlines `#[rustc_force_inline]` functions, so other bodies are never leaves.
fn is_leaf(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    if !is_force_inline(tcx, def_id.to_def_id()) {
        return false;
    }
    let (calls, mentions) = tcx.mir_inliner_callees(InstanceKind::Item(def_id.to_def_id()));
    mentions.is_empty()
        && calls.iter().all(|&(callee, args)| {
            (!callee.is_local() || tcx.is_constructor(callee)) && !args_mention_local(args)
        })
}

/// Local bodies whose optimized MIR the inliner may request when optimizing `def_id`, as far as
/// can be predicted.
fn edges<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> FxIndexSet<LocalDefId> {
    let mut collector = EdgeCollector {
        tcx,
        // Resolution erases the regions of its whole input every time, which is expensive for
        // large where-clauses, so the environment is erased once here.
        typing_env: tcx.erase_and_anonymize_regions(ty::TypingEnv::post_analysis(tcx, def_id)),
        edges: FxIndexSet::default(),
        looked_into: FxHashSet::default(),
        mentioned: FxHashSet::default(),
    };
    for &(callee, args) in tcx.mir_inliner_callees(InstanceKind::Item(def_id.to_def_id())).0 {
        collector.call(callee, args, 0);
    }
    collector.edges
}

struct EdgeCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    edges: FxIndexSet<LocalDefId>,
    /// Generic callees whose calls were already instantiated, so that each is expanded once.
    looked_into: FxHashSet<Instance<'tcx>>,
    /// Types already searched for callable items.
    mentioned: FxHashSet<Ty<'tcx>>,
}

/// How many levels of generic callees to look through.
const LOOK_THROUGH_DEPTH: usize = 3;

impl<'tcx> EdgeCollector<'tcx> {
    /// A call the caller's inliner may resolve, the items its arguments mention, and the calls the
    /// inliner would find after inlining a generic callee: callbacks and trait methods only
    /// resolve once instantiated.
    fn call(&mut self, callee: DefId, args: GenericArgs<'tcx>, depth: usize) {
        let tcx = self.tcx;
        // These args come from analysis MIR (or from instantiating a generic body), where aliases
        // may be marked rigid that aren't rigid after analysis, e.g. opaque types.
        let Ok(args) = tcx.try_normalize_erasing_regions(
            self.typing_env,
            ty::set_aliases_to_non_rigid(tcx, args),
        ) else {
            return;
        };
        self.mention(args);
        let Some(instance) = self.resolve(callee, args) else { return };
        match instance.def {
            InstanceKind::Item(def_id) => {
                self.edges.extend(def_id.as_local());
                // Deeper levels only look into fully concrete instances. With parameters, a callee's
                // body may not type-check once instantiated in this caller's environment (see
                // #146965), and resolving calls in it can then ICE. The inliner never gets there,
                // because it validates a callee body before inlining it.
                if depth < LOOK_THROUGH_DEPTH
                    && (depth == 0 || !instance.args.has_param())
                    && instance.args.non_erasable_generics().next().is_some()
                    && (def_id.is_local() || args_mention_local(instance.args))
                    && self.can_look_into(def_id)
                    && self.looked_into.insert(instance)
                {
                    for &(inner, inner_args) in tcx.mir_inliner_callees(instance.def).0 {
                        let inner_args = ty::EarlyBinder::bind(tcx, inner_args)
                            .instantiate(tcx, instance.args)
                            .skip_normalization();
                        self.call(inner, inner_args, depth + 1);
                    }
                }
            }
            InstanceKind::Intrinsic(def_id) => {
                // The inliner may inline the fallback body instead.
                self.edges.extend(def_id.as_local());
            }
            InstanceKind::Shim(ShimKind::DropGlue(_, ty)) => {
                // Inlined drop glue calls the type's own destructor. Fields are dropped by `Drop`
                // terminators, which the inliner doesn't inline.
                if let Some(ty) = ty
                    && let ty::Adt(adt, _) = *ty.kind()
                    && let Some(dtor) = tcx.adt_destructor(adt.did())
                {
                    self.edges.extend(dtor.did.as_local());
                }
            }
            InstanceKind::Shim(_) => self.edges.extend(instance.def_id().as_local()),
            InstanceKind::LlvmIntrinsic(_) | InstanceKind::Virtual(..) => {}
        }
    }

    /// `Instance::try_resolve`, minus erasing the already erased environment again.
    fn resolve(&self, def_id: DefId, args: GenericArgs<'tcx>) -> Option<Instance<'tcx>> {
        let tcx = self.tcx;
        if tcx.sess.opts.unstable_opts.enforce_type_length_limit {
            return Instance::try_resolve(tcx, self.typing_env, def_id, args).ok().flatten();
        }
        tcx.resolve_instance_raw(self.typing_env.as_query_input((def_id, args))).ok().flatten()
    }

    fn can_look_into(&self, def_id: DefId) -> bool {
        let tcx = self.tcx;
        match def_id.as_local() {
            Some(local) => is_graph_candidate(tcx, local),
            None => {
                tcx.def_kind(def_id).is_fn_like()
                    && !tcx.is_coroutine(def_id)
                    && tcx.is_mir_available(def_id)
            }
        }
    }

    /// Functions and closures whose type a body mentions are likely called through generic code,
    /// so a function item counts as a call. Mentioning an ADT doesn't lead to its destructor (see
    /// the drop glue case of `call`).
    fn mention(&mut self, args: GenericArgs<'tcx>) {
        for ty in args.types() {
            if !self.mentioned.insert(ty) {
                continue;
            }
            for ty in ty.walk().filter_map(|arg| arg.as_type()) {
                match *ty.kind() {
                    ty::FnDef(def_id, args) => {
                        if let Some(args) = args.no_bound_vars() {
                            self.call(def_id, args, LOOK_THROUGH_DEPTH);
                        }
                    }
                    ty::Closure(def_id, _) | ty::CoroutineClosure(def_id, _) => {
                        self.edges.extend(def_id.as_local());
                    }
                    _ => {}
                }
            }
        }
    }
}

rustc_index::newtype_index! {
    #[orderable]
    struct Node {}
}

rustc_index::newtype_index! {
    #[orderable]
    struct Scc {}
}

pub(crate) fn mir_inliner_order(tcx: TyCtxt<'_>, (): ()) -> FxIndexMap<LocalDefId, usize> {
    let nodes: FxIndexSet<LocalDefId> = tcx
        .hir_body_owners()
        .filter(|&def_id| is_graph_candidate(tcx, def_id) && !is_leaf(tcx, def_id))
        .collect();
    // The inliner rejects these callees before consulting the order, so edges to them would only
    // make the order coarser.
    let inlinable: Vec<bool> = nodes
        .iter()
        .map(|&def_id| {
            let attrs = tcx.codegen_fn_attrs(def_id);
            !matches!(attrs.inline, InlineAttr::Never)
                && !matches!(attrs.optimize, OptimizeAttr::DoNotOptimize)
                && crate::check_inline::is_inline_valid_on_fn(tcx, def_id.to_def_id()).is_ok()
        })
        .collect();
    let mut edge_pairs = Vec::new();
    for (index, &def_id) in nodes.iter().enumerate() {
        for target in edges(tcx, def_id) {
            if let Some(target) = nodes.get_index_of(&target)
                && inlinable[target]
            {
                edge_pairs.push((Node::new(index), Node::new(target)));
            }
        }
    }
    let graph = VecGraph::<Node>::new(nodes.len(), edge_pairs);
    let sccs = Sccs::<Node, Scc>::new(&graph);
    let mut heights: IndexVec<Scc, usize> = IndexVec::with_capacity(sccs.num_sccs());
    // Successors come first in this iteration order.
    for scc in sccs.all_sccs() {
        let height = sccs
            .successors(scc)
            .iter()
            .filter(|&&succ| succ != scc)
            .map(|&succ| heights[succ] + 1)
            .max()
            .unwrap_or(0);
        heights.push(height);
    }
    nodes
        .iter()
        .enumerate()
        .map(|(index, &def_id)| (def_id, heights[sccs.scc(Node::new(index))]))
        .collect()
}
