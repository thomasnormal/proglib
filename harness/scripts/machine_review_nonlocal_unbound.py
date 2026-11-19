# Machine review row: nonlocal with no enclosing binding is a SyntaxError in CPython: refused.
def f():
    nonlocal x
    x = 1


f()
print("ran")
