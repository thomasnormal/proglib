"""Machine argument-binder row: an earlier default is omitted before a keyword."""

def combine(x=10, y=20):
    return x + y

print(combine(y=7))
