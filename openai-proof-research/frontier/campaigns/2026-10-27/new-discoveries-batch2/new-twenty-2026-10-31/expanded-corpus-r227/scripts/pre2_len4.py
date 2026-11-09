import sys, math, itertools, json
# 364481 diagnostic: length-4 partitions x with y_i = sqrt(prod x)/x_i integral,
# sum y = sum x, y != x as multisets. Then pre_2(x) = pre_2(y) (y_i y_j = x_k x_l).
M = int(sys.argv[1])
found = []
for x in itertools.combinations_with_replacement(range(1, M + 1), 4):
    P = x[0] * x[1] * x[2] * x[3]
    r = math.isqrt(P)
    if r * r != P:
        continue
    if any(r % a for a in x):
        continue
    y = tuple(sorted(r // a for a in x))
    if sum(y) == sum(x) and y != x and x < y:
        found.append((x, y))
def pre2(l):
    return sorted(a * b for a, b in itertools.combinations(l, 2))
for x, y in found[:20]:
    assert pre2(x) == pre2(y)
    print(sum(x), x, y, pre2(x))
print(json.dumps({'max_part': M, 'pairs': len(found)}))
