class Left:
    def __init__(self):
        self.value = 1
class Right:
    def __init__(self):
        self.value = 2
class Child(Left, Right):
    pass
print(Child().value)
