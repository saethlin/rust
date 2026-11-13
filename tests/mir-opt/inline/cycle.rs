// EMIT_MIR_FOR_EACH_PANIC_STRATEGY
//@ compile-flags: -Zinline-mir-hint-threshold=1000 -C debuginfo=full

// EMIT_MIR cycle.f.Inline.diff
#[inline(always)]
fn f(g: impl Fn()) {
    // CHECK-LABEL: fn f(
    // CHECK-NOT: inlined
    g();
}

// EMIT_MIR cycle.g.Inline.diff
#[inline(always)]
fn g() {
    // `main` and `g` mention each other, so neither may inline the other. Whether `g` inlines
    // `f` depends on the panic strategy (forwarder cost threshold).
    // CHECK-LABEL: fn g(
    // CHECK-NOT: (inlined main)
    f(main);
}

// EMIT_MIR cycle.main.Inline.diff
fn main() {
    // CHECK-LABEL: fn main(
    // CHECK: (inlined f::<fn() {g}>)
    // CHECK-NOT: (inlined g)
    f(g);
}
