"""Machine argument-binder row: positional-only binding precedes *args."""

def choose(prefix, /, *args):
    return prefix + args[0]

print(choose(1, 2))
