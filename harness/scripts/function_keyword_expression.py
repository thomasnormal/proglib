"""Machine argument-binder row: a keyword value is evaluated before binding."""

def answer(x):
    return x

print(answer(x=3 + 4))
