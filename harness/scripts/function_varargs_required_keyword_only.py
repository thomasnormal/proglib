"""Machine argument-binder row: *args precedes a required keyword-only parameter."""

def combine(prefix, *args, suffix):
    return prefix + args[0] + suffix

print(combine(1, 2, 3, suffix=4))
