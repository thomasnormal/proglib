class A:
    def m(self):
        return 1


a = A()
a.m = 5
print(a.m)
