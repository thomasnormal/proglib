class A:
    items = []


a = A()
b = A()
a.items.append(1)
print(len(b.items))
