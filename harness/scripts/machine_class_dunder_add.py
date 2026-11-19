class Box:
    def __add__(self, other):
        return other + 5
print(Box() + 2)
