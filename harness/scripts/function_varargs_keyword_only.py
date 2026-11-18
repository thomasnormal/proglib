"""Machine argument-binder row: *args precedes a keyword-only parameter."""

def combine(prefix, *args, suffix=1):
    return prefix + args[0] + suffix

print(combine(1, 2, 3, suffix=4))
print(combine(1, 2, 3))
