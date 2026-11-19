"""Machine argument-binder row: defaults read globals at definition time."""

base = 3

def answer(x=base + 4):
    return x

base = 100
print(answer())
