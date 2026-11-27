# Undefined child in an inactive generate arm

IEEE 1800-2023 §27.5 instantiates only the selected generate branch. At
`USE_VENDOR=0`, the ordinary route therefore loads the portable assignment and
the undefined child remains in the retained source-shaped inactive arm. At
`USE_VENDOR=1`, the selected child is an explicit unsupported process and the
memory admission predicate refuses the point. The receipt covers the default
rows `0->0`, `1->1`, `x->x`, and `z->z` on Icarus Verilog 13.0 and Xcelium
26.09-s001.
