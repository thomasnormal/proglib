"""Machine argument-binder row: multiple keyword-only parameters follow *args."""

def combine(*args, suffix, extra=2):
    return args[0] + suffix + extra

print(combine(1, suffix=4))
print(combine(1, suffix=4, extra=5))
