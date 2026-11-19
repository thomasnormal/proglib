# Machine review row: an item appended during the loop is visited (live list iterator).
xs = [1, 2]
for x in xs:
    if x == 1:
        xs.append(3)
    print(x)
