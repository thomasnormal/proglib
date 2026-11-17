"""The admitted single-clause dictionary-comprehension surface."""


def from_range(n, probe):
    values = {i: i * i for i in range(n)}
    return (len(values), values.get(probe, -1))


def duplicate_keys(n):
    values = {i % 2: i for i in range(n)}
    return (values[0], values[1])


def bad_pair():
    return len(dict(x for x in [1]))


def bad_length():
    return len(dict((x,) for x in [1]))


def unhashable_key():
    return len({[1, 2]: 3 for _ in [0]})


def walrus_value_leak():
    y = 0
    values = {x: (y := x + 10) for x in range(3)}
    return y


def target_leak_on_exception():
    x = 99
    try:
        {x: 1 / 0 for x in [1]}
    except ZeroDivisionError:
        return x


def mutate_iterable():
    xs = [1, 2, 3]
    return len({x: xs.pop() for x in xs})


def empty_comp():
    return {x: x for x in []}


def exception_key():
    return {1 / 0: x for x in [1]}


def exception_value():
    return {x: 1 / 0 for x in [1]}
