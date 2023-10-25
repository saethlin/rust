//@ compile-flags: -Copt-level=3 -Zpanic-is-ub

#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub fn index(x: &[u8], idx: usize) -> &u8 {
    // CHECK-LABEL: @index(
    // CHECK-NEXT: start:
    // CHECK-NEXT: icmp ult
    // CHECK-NEXT: tail call void @llvm.assume
    // CHECK-NEXT: getelementptr inbounds nuw
    // CHECK-NEXT: ret ptr
    &x[idx]
}

#[unsafe(no_mangle)]
pub fn divide(x: i64, y: i64) -> i64 {
    // CHECK-LABEL: @divide(
    // CHECK-NEXT: start:
    // CHECK-NEXT: icmp ne i64
    // CHECK-NEXT: icmp ne i64
    // CHECK-NEXT: or i1
    // CHECK-NEXT: tail call void @llvm.assume
    // CHECK-NEXT: sdiv i64
    // CHECK-NEXT: ret i64
    x / y
}
