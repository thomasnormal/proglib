# Machine review row: `del x` in a function removes the local only, not the module's x.
x = 1


def f():
    x = 2
    del x
    return 0


f()
print(x)
