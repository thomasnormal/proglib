"""A top-level unsupported try shape must refuse, never roll back and continue."""
try:
    print("before")
except Exception:
    print("caught")
else:
    print("else")
