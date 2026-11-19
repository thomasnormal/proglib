class Box:
    value = 3
    def get(self, *, extra=2):
        return self.value + extra
b = Box()
print(b.get())
