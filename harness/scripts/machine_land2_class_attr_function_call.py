def helper(self):
    return 9


class A:
    m = helper


print(A().m())
