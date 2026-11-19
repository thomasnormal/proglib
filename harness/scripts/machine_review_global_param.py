# Machine review row: a parameter declared global is a SyntaxError in CPython: refused.
def f(x):
    global x
    return 1


print(f(2))
