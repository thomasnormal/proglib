"""Machine expression-call row: a local assignment in the callee."""

def inc(x):
    y = x + 1
    return y

print(inc(4))
