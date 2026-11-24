# Signed packed bit-select receipt

This source exercises IEEE 1800-2023 §§6.11 and 11.8.2. A bit select of a
signed packed vector remains a one-bit unsigned value, including when the
selected vector contains x/z bits. Canonical E and both pinned simulators
match the three rows.
