# Sampled `$onehot` witness

This source-shaped fixture checks the finite SVA `$onehot` predicate on two
sampled clock edges. The contract returns true only when exactly one sampled
bit is one. Unknown vectors remain unresolved when no known one already makes
the predicate false, following IEEE 1800-2023 §16.9.4.
