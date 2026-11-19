# Machine review row: `x += 1` in a function where x is only global: CPython UnboundLocalError, refused.
x = 1


def f():
    x += 1
    return x


print(f())
