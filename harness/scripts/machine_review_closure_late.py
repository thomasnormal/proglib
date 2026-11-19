# Machine review row: a closure reads the enclosing variable's value at call time.
def g():
    v = 1

    def h():
        return v
    v = 2
    return h()


print(g())
