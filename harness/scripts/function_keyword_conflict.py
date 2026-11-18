"""Machine argument-binder row: duplicate positional/keyword binding refuses."""

def add(x, y):
    return x + y

add(3, x=2)
