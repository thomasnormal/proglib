"""Frozen-runner regression row: keyword-only parameters."""

def answer(*, x):
    print(x)

answer(7)
