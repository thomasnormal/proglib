"""A walrus inside a starred list display binds in the function, so `y` is a local of f and the read raises
UnboundLocalError even though the display never runs."""

y = 5


def f():
    if False:
        xs = [*(), (y := 1)]
    return y


print(f())
