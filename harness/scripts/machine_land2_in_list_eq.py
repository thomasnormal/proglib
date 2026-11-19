class A:
    def __eq__(self, other):
        return True


print(1 in [A()])
