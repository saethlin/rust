//@ build-pass
//@ compile-flags: -Copt-level=2
// Regression test for #161234. Every member of this strongly connected call graph is a cycle
// peer of every other, so the inliner must never request the optimized MIR of a peer.

#[inline(never)]
fn black_box(x: u32) -> u32 {
    std::hint::black_box(x)
}

fn a(n: u32) -> u32 {
    if n == 0 { black_box(0) } else { b(n - 1) + c(n - 1) }
}

fn b(n: u32) -> u32 {
    if n == 0 { black_box(1) } else { a(n - 1) + d(n - 1) }
}

fn c(n: u32) -> u32 {
    if n == 0 { black_box(2) } else { d(n - 1) + b(n - 1) }
}

fn d(n: u32) -> u32 {
    if n == 0 { black_box(3) } else { c(n - 1) + a(n - 1) }
}

fn main() {
    println!("{}", a(black_box(10)));
}
