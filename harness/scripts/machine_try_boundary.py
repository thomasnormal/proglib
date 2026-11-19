try:
    x = 1
except ValueError as exc:
    x = 2
else:
    x = 3
finally:
    x += 1
print(x)
