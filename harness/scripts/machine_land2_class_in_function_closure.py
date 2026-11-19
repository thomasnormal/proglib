x = "global"


def f():
    x = "local"

    class A:
        def m(self):
            return x
    return A().m()


print(f())
