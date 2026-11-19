class Box:
    def __contains__(self, value):
        return value == 2
print(2 in Box())
