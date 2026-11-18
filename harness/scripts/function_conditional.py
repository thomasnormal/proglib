"""Machine scopes row: a lazy conditional in a function return."""

def select(x):
    return 1 if x else 2

select(0)
