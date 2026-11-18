"""Frozen-runner regression row: positional-only parameters."""

def answer(x, /):
    return x

print(answer(x=7))
