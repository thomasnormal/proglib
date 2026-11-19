try:
    raise ValueError(1)
except ValueError as error:
    print(1)
except TypeError:
    print(2)
else:
    print(3)
finally:
    print(4)
