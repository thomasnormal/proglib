"""Frozen-runner regression row: variadic positional parameters."""

def answer(*args):
    return args

print(answer(1))
