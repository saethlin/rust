//@ incremental
//@ compile-flags: -Cno-prepopulate-passes -Csymbol-mangling-version=v0 -Zinline-mir=no -Copt-level=0

#![crate_type = "lib"]

pub fn f() {
    let c = || {
        let mut a = [0, 1, 2, 3, 4, 5, 6];
        a[0] = 0;
        a[1] = 0;
        a[2] = 0;
        a[3] = 0;
        a[4] = 0;
        a[5] = 0;
        a
    };
    c();
}

// CHECK:      ; closures_without_inlinehint::f::{closure#0}
// CHECK-NOT:  ; Function Attrs: inlinehint
