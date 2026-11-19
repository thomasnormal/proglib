class A:
    def __neg__(self):
        return 3


class B(A):
    pass


print(-B())
