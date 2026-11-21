# C survey measurement, 2026-11-21

Measurement rerun at **2026-11-21 04:20 UTC** used the current `c-torture-run`
binary after a successful rebuild under `MemoryMax=24G` and one Lean thread.

The required full replay was attempted after rebuilding `c-torture-run` from
the current tree under the lane's 24 GiB cgroup.  The rebuild completed
successfully and `coredumpctl` reported zero Lean coredumps in the preceding
two hours.

Fresh envelope regeneration remains blocked.  The host has the pinned Clang
21.1.8 runtime but no Clang development headers, so the approved probe cannot
be rebuilt.  The available probe binaries use the former stdout JSON protocol,
while the current extractor requires one same-invocation node-id record on
stderr.  A direct current-extractor run therefore stops with `structured type
plugin did not return exactly one node-id record`.  No current C-MATCH number
is claimed.

For diagnosis only, the current batch runner replayed all 2,214 rows against
the stale envelope manifest.  The current extractor rejected 350 rows at the
frontend and marked 1,864 parsed rows `not-ingested` for a stale extractor
hash.  This result is an instrument check, not a survey receipt.

The last valid structured-envelope receipt remains 625 MATCH / 2,214 rows,
with 625 active matches over the 2,128-row denominator after no-entry-point
rows.  The 2026-11-20 receipt records the 701 names lost against the 1,326
receipt, including 490 structured-plugin instrument changes, 2 correct UB
refusals, and 209 rows requiring regression classification.

The next valid measurement requires a Clang development package or a rebuilt
`structured_type_probe.so` that implements the current stderr protocol.  The
last valid structured-envelope receipt remains **625 MATCH / 2,214 rows**
(625/2,128 after no-entry-point rows).  The 701 names lost against the
1,326 receipt remain classified in
[`c-survey-20261120-measurement.json`](c-survey-20261120-measurement.json):
490 instrument changes, 2 correct UB refusals and 209 regressions.  The
reported 213 rejected-file increase is not reproduced by the available
receipts.  No survey delta or S1 gate result is asserted from this run.

The S1 gate audit on 2026-11-21 reports zero type-string operations, zero
legacy `CType` aliases, and no `torScalarSize`, `sizeAlign`, `recordsOf`,
`isPtrType`, `isPtrIntType` or `cAliasCompatible` definitions in the C lane.
The approved structured probe's determinism self-test passes with 88 records,
but the current extractor rejects that binary because it emits the former
stdout protocol rather than the required stderr node-id record. No Clang
development headers are installed to rebuild the probe, so the S1 survey gate
remains unmeasured.
