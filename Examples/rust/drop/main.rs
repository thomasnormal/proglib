struct D;
impl Drop for D {
    fn drop(&mut self) {}
}
fn main() {
    let _d = D;
}
