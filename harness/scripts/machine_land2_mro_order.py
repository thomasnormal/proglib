class A:
    def m(self):
        return "A"


class B:
    def m(self):
        return "B"


class C(A, B):
    pass


print(C().m())
