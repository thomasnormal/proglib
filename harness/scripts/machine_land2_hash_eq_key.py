class A:
    def __eq__(self, other):
        return True


d = {}
d[A()] = 1
print(len(d))
