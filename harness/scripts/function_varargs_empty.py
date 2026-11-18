"""Machine argument-binder row: empty *args preserves tuple indexing errors."""

def answer(*args):
    return args[0]

print(answer())
