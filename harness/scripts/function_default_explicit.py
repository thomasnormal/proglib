"""Machine scopes row: an explicit argument overrides a literal default."""

def answer(x=42):
    return x

print(answer(7))
