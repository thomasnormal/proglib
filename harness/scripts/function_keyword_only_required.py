"""Machine argument-binder row: a required keyword-only parameter is supplied."""

def answer(*, x):
    return x

print(answer(x=7))
