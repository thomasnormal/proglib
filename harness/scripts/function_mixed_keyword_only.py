"""Machine argument-binder row: positional and keyword-only parameters mix."""

def combine(x, *, y=2):
    return x + y

print(combine(3, y=4))
print(combine(3))
