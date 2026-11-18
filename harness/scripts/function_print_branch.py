"""Machine expression-call row: a branch in the callee selects the return."""

def choose(x):
    if x:
        return 1
    else:
        return 2

print(choose(0))
