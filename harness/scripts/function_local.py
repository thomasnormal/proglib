"""Machine scopes row: local assignment before a function return."""

def inc(x):
    y = x + 1
    return y

inc(4)
