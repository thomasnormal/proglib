class Box:
    def __truediv__(self, other):
        return other + 5
print(Box() / 2)
