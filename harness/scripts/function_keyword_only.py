"""Machine argument-binder row: keyword-only parameters remain an explicit refusal."""

def answer(*, x=7):
    return x

print(answer(x=3))
