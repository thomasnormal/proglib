"""Machine wrong-answer row: a user definition shadows print."""

def print(value):
    return 99

print(1)
