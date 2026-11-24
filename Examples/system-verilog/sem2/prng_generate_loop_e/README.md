# Clocked generate-loop profile boundary

The source-shaped child instances in a literal `for` generate loop load and
run through ordinary E under IEEE 1800-2023 §§23.3.3 and 27.4. The clocked
`sv_structure` instantiation profile retains its named refusal for `for`
generate expansion. The pinned simulators disagree on the first active edge
for this child-array source, so no simulator agreement is claimed.
