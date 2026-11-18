"""Machine argument-binder row: fixed positional binding precedes *args."""

def choose(prefix, *args):
    return args[1]

print(choose(0, 7, 8))
