# Generate-if inside generate-for naming refusal

The symbolic envelope refuses a declaration inside a generate-if nested in a
generate-for before the template instance name can be copied to another
iteration. This is a loud boundary for IEEE 1800-2023 §§27.4-27.6. The
neutral `w2g` row previously loaded at `N=2` while naming the second variable
`g[0].a1.t` instead of `g[1].a1.t`. The receipt checks
`GenerateDecl:instance-name` through the ordinary loader.
