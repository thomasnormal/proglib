"""Machine expression-call row: several local assignments in the callee."""

def total(x):
    y = x + 1
    z = y + 1
    return z

print(total(4))
