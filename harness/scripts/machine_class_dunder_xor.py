class Box:
    def __xor__(self, other):
        return other + 5
print(Box() ^ 2)
