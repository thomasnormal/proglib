class Box:
    def __init__(self, *, value=5):
        self.value = value
b = Box(value=7)
print(b.value)
