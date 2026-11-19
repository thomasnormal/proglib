# Machine review row: a module-level tuple assignment rebinds a module name bound before.
a = 0
a, b = 1, 2
print(a)
