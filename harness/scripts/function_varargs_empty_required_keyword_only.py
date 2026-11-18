"""Machine argument-binder row: empty *args with a supplied required keyword-only parameter."""

def answer(*args, suffix):
    return suffix

print(answer(suffix=7))
