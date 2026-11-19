# Machine review row: a loop variable of an empty loop is unbound (UnboundLocalError): refused.
def f():
    for i in ():
        pass
    return i


print(f())
