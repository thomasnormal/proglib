# Machine review row: assignment in a nested function without nonlocal binds its own local.
def outer():
    v = 1

    def inner():
        v = 2
        return v
    r = inner()
    print(r, v)


outer()
