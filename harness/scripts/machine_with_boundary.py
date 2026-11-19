class Ctx:
    def __enter__(self):
        return 1
    def __exit__(self, typ, value, tb):
        return False
with Ctx() as x:
    print(x)
