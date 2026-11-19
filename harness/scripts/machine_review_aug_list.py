# Machine review row: `x += [2]` on a list (in place in CPython): refused.
x = [1]
x += [2]
print(len(x))
