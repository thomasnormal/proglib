"""Machine scopes row: a literal default parameter is used when omitted."""

def answer(x=42):
    return x

print(answer())
