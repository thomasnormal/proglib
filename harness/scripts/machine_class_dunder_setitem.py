class Box:
    def __setitem__(self, index, value):
        self.value = value
b = Box()
b[2] = 7
print(b.value)
