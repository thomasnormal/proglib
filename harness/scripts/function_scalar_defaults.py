"""Machine argument-binder row: boolean, string, and None literal defaults."""

def bool_default(value=True):
    return value

def string_default(value="ok"):
    return value

def none_default(value=None):
    return value

print(bool_default())
print(string_default())
print(none_default())
