class Base:
    def value(self):
        return 7
class Child(Base):
    pass
b = Child()
print(b.value())
