# Machine review row: assignment in a module-level function binds a local, not the module's name.
x = 1


def f():
    x = 2
    return x


print(f())
print(x)
