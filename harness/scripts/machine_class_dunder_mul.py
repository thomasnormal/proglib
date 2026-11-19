class Box:
    def __mul__(self, other):
        return other + 5
print(Box() * 2)
