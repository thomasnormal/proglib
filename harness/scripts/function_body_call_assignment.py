"""Machine function row: a function body assigns the result of a named call."""

def increment(x):
    return x + 1

def wrapper(x):
    value = increment(x)
    return value

print(wrapper(6))
