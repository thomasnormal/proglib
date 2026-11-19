y = 1


def f():
    y = 2

    class A:
        z = y
    return A.z


print(f())
