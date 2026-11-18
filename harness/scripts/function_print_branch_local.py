"""Machine expression-call row: a selected branch assigns before returning."""

def choose(x):
    if x:
        y = 1
        return y
    else:
        return 2

print(choose(1))
