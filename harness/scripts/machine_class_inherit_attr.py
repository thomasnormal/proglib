class Base:
    value = 7
class Child(Base):
    pass
b = Child()
print(b.value)
print(Child.value)
