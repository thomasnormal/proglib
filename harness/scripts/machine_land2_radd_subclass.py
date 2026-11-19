class A:
    def __add__(self, other):
        return 1


class B(A):
    def __radd__(self, other):
        return 2


print(A() + B())
