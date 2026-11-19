def consume():
    value = yield 5
    return value

def delegate(source):
    value = yield from source
    return value

consume()
