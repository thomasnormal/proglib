"""Machine wrong-answer row: a module function is redefined."""

def value():
    return 1

print(value())

def value():
    return 2

print(value())
