fn main() {
    unsafe {
        let pointer = std::ptr::null::<u8>();
        std::hint::black_box(pointer.read());
    }
}
