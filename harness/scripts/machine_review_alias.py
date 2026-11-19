# Machine review row: a list mutated through an alias is seen through the other name.
xs = [1, 2]
ys = xs
ys.append(3)
print(len(xs))
