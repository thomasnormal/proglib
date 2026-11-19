def outer():
    x = 1

    def inner():
        print(x)
        x = 2
    inner()


outer()
