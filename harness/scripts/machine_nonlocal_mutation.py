"""Machine scope row: a nonlocal augmented assignment updates its cell."""

def outer():
    value = 1

    def bump():
        nonlocal value
        value += 1
        return value

    bump()
    return value

print(outer())
