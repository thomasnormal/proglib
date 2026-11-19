# Machine review row: a function reads a module global bound after its definition.
def f():
    return y


y = 3
print(f())
