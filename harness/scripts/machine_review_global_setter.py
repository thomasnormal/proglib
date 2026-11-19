# Machine review row: a function reads a global another function set under `global`.
x = 1


def setx():
    global x
    x = 5


def getx():
    return x


setx()
print(getx())
