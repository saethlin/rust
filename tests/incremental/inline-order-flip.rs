// The MIR inlining order changes between sessions while the bodies whose optimized MIR may be
// reused stay the same: `a -> b -> c` becomes the cycle `a -> b -> c -> a`, then a chain again.
// Reused optimized MIR must not request MIR against the new order (that would be a query cycle).

//@ revisions: rpass1 rpass2 rpass3
//@ compile-flags: -Z query-dep-graph -Z inline-mir -C opt-level=2
//@ ignore-backends: gcc

#[inline(never)]
fn sink(x: u32) -> u32 {
    std::hint::black_box(x)
}

fn a(x: u32) -> u32 {
    if x == 0 { sink(1) } else { b(x - 1) + 1 }
}

fn b(x: u32) -> u32 {
    if x == 0 { sink(2) } else { c(x - 1) * 2 }
}

#[cfg(not(rpass2))]
fn c(x: u32) -> u32 {
    sink(x) + 3
}

#[cfg(rpass2)]
fn c(x: u32) -> u32 {
    if x == 0 { sink(3) } else { a(x - 1) + 3 }
}

fn main() {
    assert_eq!(a(sink(3)), 9);
}
