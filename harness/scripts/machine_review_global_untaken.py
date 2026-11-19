# Machine review row: a global declaration in an untaken branch still applies in CPython: refused.
x = 0


def f():
    if False:
        global x
    x = 1


f()
print(x)
