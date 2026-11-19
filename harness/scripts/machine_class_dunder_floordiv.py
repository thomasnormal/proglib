class Box:
    def __floordiv__(self, other):
        return other + 5
print(Box() // 2)
