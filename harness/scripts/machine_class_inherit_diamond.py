class Root:
    value = 1
class Left(Root):
    pass
class Right(Root):
    pass
class Child(Left, Right):
    pass
print(Child.value)
