"""Machine argument-binder row: positional-only, *args, and keyword-only binding."""

def combine(prefix, /, *args, suffix=2):
    return prefix + args[0] + suffix

print(combine(1, 3))
print(combine(1, 3, suffix=4))
