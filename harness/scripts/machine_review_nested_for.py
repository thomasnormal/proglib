# Machine review row: a loop nested in a loop body resumes the outer loop.
for i in (1, 2):
    for j in (3, 4):
        print(i, j)
print("done")
