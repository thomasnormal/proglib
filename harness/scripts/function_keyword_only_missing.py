"""Machine argument-binder row: omitting a required keyword-only parameter."""

def answer(*, x):
    return x

print(answer())
