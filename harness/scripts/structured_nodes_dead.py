"""Set displays, expression lambdas, async for and async with in code that never runs.

The extractor keeps these as CPython's own AST nodes for the machine. The
compatibility decoder must still load the module and refuse them only when
they are reached, as it did when they arrived as Unsupported nodes.
"""


def unused_set():
    return {1, 2}


def unused_lambda():
    return sorted([3, 1], key=lambda x: -x)


async def unused_async_for(xs):
    async for x in xs:
        pass


async def unused_async_with(manager):
    async with manager:
        pass


print("ok")
