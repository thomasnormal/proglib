class A:
    def __eq__(self, other):
        return False


a = A()
print(a == a)
