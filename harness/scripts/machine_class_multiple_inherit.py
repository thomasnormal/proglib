class Left:
    value = 1
class Right:
    value = 2
class Child(Left, Right):
    pass
print(Child.value)
