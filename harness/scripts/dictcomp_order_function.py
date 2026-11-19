"""A dictionary comprehension keeps insertion order (list(d) of a comprehension in a function body)."""

def f():
    d = {k: k + 1 for k in (3, 1, 2)}
    return list(d)


print(f())
