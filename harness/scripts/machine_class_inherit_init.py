class Base:
    def __init__(self, value):
        self.value = value
class Child(Base):
    pass
b = Child(9)
print(b.value)
