# Fresh C replay receipt — 2026-11-28

The pinned Clang 21.1.8 toolchain and all four approved parser plugins were
loaded from the host's pinned Clang 21.1.8 environment script (`env.sh`). The gate ran
with one Lean thread and a 24 GiB cgroup.

The approved offline manifest for the 300-row C1 gate found **0 parsed source
files and 300 absent files** in the external cache. The fresh replay therefore
scored **0/300**, with all 300 rows `not-fetched` and no MATCH, DIVERGE,
REFUSE, UB, timeout, or runner verdicts. The gate's designed degradation path
left the committed full survey and admitted-subset pages unchanged.

No cached-envelope loss can be attributed to the extractor from this run.
There were no cached envelopes available to compare. The prior committed full
receipt remains the authoritative 2,214-row measurement until the GPL corpus
cache is supplied outside the repository.

Checks passed during the gate, including `tools/leanc --self-test`, the C
survey self-test, extractor self-test, all four parser-plugin determinism
checks, the divergence register, and the F2 replay check.
