"""Machine argument-binder row: keyword order is independent after *args."""

def combine(*args, suffix, extra=2):
    return args[0] + suffix + extra

print(combine(1, extra=5, suffix=4))
