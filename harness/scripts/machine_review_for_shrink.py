# Machine review row: an item popped during the loop is not visited (live list iterator).
xs = [1, 2, 3]
for x in xs:
    if x == 1:
        xs.pop()
    print(x)
