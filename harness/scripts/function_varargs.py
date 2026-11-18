"""Machine argument-binder row: variadic positional parameters remain an explicit refusal."""

def answer(*args):
    return args[0]

print(answer(7))
