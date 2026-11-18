"""Machine wrong-answer row: an assignment shadows a function name."""

value = 5

def value():
    return 1

print(value())
