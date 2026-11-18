"""Machine scopes row: a function with no explicit return resumes its caller."""

def touch():
    pass

touch()
print("after")
