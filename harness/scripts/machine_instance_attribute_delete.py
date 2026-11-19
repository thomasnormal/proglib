class Box:
    value = 3
b = Box()
b.value = 4
del b.value
print(b.value)
