# Procedural-for indexed-target refusal receipt

This clean-room source keeps a module-level loop variable and a fixed unpacked
array target in an `always_ff` process. Slang retains the source-shaped loop,
but canonical E refuses the indexed procedural target as
`AssignmentExpression:target` instead of inventing array storage semantics.
The unchanged source executes four rows on both pinned simulators.
