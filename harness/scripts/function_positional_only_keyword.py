"""Machine argument-binder row: keyword use of a positional-only parameter."""

def answer(x, /):
    return x

print(answer(x=7))
