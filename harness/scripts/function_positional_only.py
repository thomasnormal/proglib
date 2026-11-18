"""Machine argument-binder row: positional-only parameters remain an explicit refusal."""

def answer(x, /):
    return x

print(answer(7))
