class A:
    def __len__(self):
        return 0


print("yes" if A() else "no")
