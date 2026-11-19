"""A walrus inside a two-clause list comprehension binds in the enclosing function (PEP 572), so `y` is a
local of f and the read raises UnboundLocalError even though the comprehension never runs."""

y = 5


def f():
    if False:
        xs = [(y := a) for a in range(2) for b in range(2)]
    return y


print(f())
