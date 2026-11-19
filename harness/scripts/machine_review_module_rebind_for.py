# Machine review row: a module-level loop rebinds a module name bound before.
i = 0
for i in (1, 2):
    pass
print(i)
