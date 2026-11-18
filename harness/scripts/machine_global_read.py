"""Machine wrong-answer row: a function reads a module global."""

value = 5

def read_value():
    return value

print(read_value())
