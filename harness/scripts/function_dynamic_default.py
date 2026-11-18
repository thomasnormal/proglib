"""Machine argument-binder row: dynamic defaults remain an explicit refusal."""

def answer(x=3 + 4):
    return x

print(answer())
