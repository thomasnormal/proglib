"""Machine argument-binder row: a keyword selects a defaulted parameter."""

def answer(x=42):
    return x

print(answer(x=7))
