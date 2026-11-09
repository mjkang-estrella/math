"""Only semantic inputs are n and length; yielded primitives are paid by the runner.

Each yield requests (x*y+acc) % n. This is explicit modular arithmetic, not a
coefficient oracle. No imports, files, factors, family labels, or binomial calls.
"""


def convolution(left, right, n, length):
    out = [0] * length
    for i in range(length):
        for j in range(length):
            k = (i + j) % length
            out[k] = yield (left[i], right[j], out[k])
    return out


def fold(n, length):
    assert n > 1 and length >= 2
    result = [1] + [0] * (length - 1)
    base = [1, 1] + [0] * (length - 2)
    exponent = n - 1
    while exponent:
        if exponent & 1:
            result = yield from convolution(result, base, n, length)
        exponent >>= 1
        if exponent:
            base = yield from convolution(base, base, n, length)
    return result
