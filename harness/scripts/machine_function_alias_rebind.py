def f():
    return 1
h = f
def f():
    return 2
print(h())
