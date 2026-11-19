total = 100


def f(items):
    for item in items:
        if item > 1:
            total = item
    return total


print(f([1, 2, 3]))
