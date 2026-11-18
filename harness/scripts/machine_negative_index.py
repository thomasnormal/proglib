"""Machine wrong-answer row: negative tuple indices count from the end."""

def last(first, second, third):
    values = (first, second, third)
    return values[-1]

print(last(1, 2, 3))
