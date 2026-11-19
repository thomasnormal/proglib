class Box:
    def __sub__(self, other):
        return other + 5
print(Box() - 2)
