xs = [1, 2]
ys = xs
xs.append(3)
print(len(ys))
print(ys[-1])
print(xs.pop())
print(len(xs))
xs[0] = 9
print(ys[0])
