"""Machine expression-call row: several assignments in a selected branch."""

def choose(x):
    if x:
        y = 1
        z = y + 1
        return z
    else:
        return 2

print(choose(1))
