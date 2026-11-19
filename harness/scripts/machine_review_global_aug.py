# Machine review row: `x += 1` under `global x` updates the module's x.
x = 1


def f():
    global x
    x += 1


f()
print(x)
