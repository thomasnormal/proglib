class Left:
    def value(self):
        return 1
class Right:
    def value(self):
        return 2
class Child(Left, Right):
    pass
print(Child().value())
