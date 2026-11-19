def outer():
    value = 1
    def update():
        nonlocal value
        value = 7
    update()
    return value

print(outer())
