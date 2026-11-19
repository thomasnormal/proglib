class Box:
    def __abs__(self):
        return -3
print(abs(Box()))
