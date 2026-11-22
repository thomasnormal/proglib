# Scalar-storage-order corpus boundary, 2026-11-22

The pinned Clang 21.1.8 accepts `20230630-2.c` and `20230630-4.c` with a warning that `scalar_storage_order` is an unknown attribute. Both tests then abort because their expected byte order requires GCC's extension. The tests exercise compiler support for that extension, rather than a C rule implemented by the pinned oracle.

The manifest now records both names as `oracle-tests-compiler` with the extension citation. `LeanModels.C.C23.Torture` accepts that classification only when the ingested envelope contains a parser-native record layout with bit-fields and an `abort` path. No source text or type spelling is re-parsed.
