class A:
    def __init__(self, x, y=2):
        self.s = x + y


print(A(y=3, x=1).s)
