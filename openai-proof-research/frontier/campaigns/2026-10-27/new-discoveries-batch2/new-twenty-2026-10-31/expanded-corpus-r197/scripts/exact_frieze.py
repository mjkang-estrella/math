"""Exact frieze computation in Z[sqrt2] for the quiddity cycle (1+r2, r2, 2r2, r2), r2 = sqrt(2).
Elements are pairs (a, b) meaning a + b*sqrt(2), a, b integers.
Prints every row m_{i,i+k} (i = 0..3) up to the first row containing a negative entry, the exact
sign proofs, the unimodular-rule check on all computed diamonds, and the monodromy trace.
usage: exact_frieze.py ROWS"""
import sys, json
ROWS = int(sys.argv[1])
def add(x, y): return (x[0] + y[0], x[1] + y[1])
def sub(x, y): return (x[0] - y[0], x[1] - y[1])
def mul(x, y): return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])
def sign(x):
    a, b = x
    # sign of a + b sqrt2, exact
    if a >= 0 and b >= 0: return (a > 0 or b > 0) and 1 or 0
    if a <= 0 and b <= 0: return -1 if (a < 0 or b < 0) else 0
    # opposite signs: compare a^2 with 2 b^2
    if a > 0:  # b < 0
        return 1 if a * a > 2 * b * b else -1
    return 1 if 2 * b * b > a * a else -1

q = [(1, 1), (0, 1), (0, 2), (0, 1)]   # 1+sqrt2, sqrt2, 2sqrt2, sqrt2  (quiddity m_{i-1,i+1} = q[i mod 4])
n = len(q)
# m[(i,j)] for i in range(-2, n+2) window large enough; m_{i,i}=0, m_{i,i+1}=1,
# m_{i,j+1} = c_j m_{i,j} - m_{i,j-1}, c_j = m_{j-1,j+1} = q[j mod n]
M = {}
I0 = range(0, n)
for i in range(-ROWS - 4, n + 4):
    M[(i, i)] = (0, 0); M[(i, i + 1)] = (1, 0)
    for j in range(i + 1, i + ROWS + 2):
        M[(i, j + 1)] = sub(mul(q[j % n], M[(i, j)]), M[(i, j - 1)])
out = {'quiddity_cycle': '(1+sqrt2, sqrt2, 2sqrt2, sqrt2)', 'rows': [], 'first_negative': None}
for k in range(2, ROWS + 2):
    row = [M[(i, i + k)] for i in I0]
    out['rows'].append({'k': k, 'entries_a_b': row, 'signs': [sign(x) for x in row]})
    neg = [(i, M[(i, i + k)]) for i in I0 if sign(M[(i, i + k)]) < 0]
    if neg and out['first_negative'] is None:
        i, x = neg[0]
        out['first_negative'] = {'i': i, 'j': i + k, 'value_a_b': x,
                                 'proof': f'{x[0]}+({x[1]})sqrt2 < 0 since sign test a^2={x[0]**2} vs 2b^2={2*x[1]**2}'}
        break
# unimodular rule (standard orientation): m_{i,j} m_{i+1,j+1} - m_{i+1,j} m_{i,j+1} = 1
bad = 0; cnt = 0
for i in range(0, n):
    for j in range(i + 1, i + k):
        if (i + 1, j) in M and (i, j + 1) in M and (i + 1, j + 1) in M:
            d = sub(mul(M[(i, j)], M[(i + 1, j + 1)]), mul(M[(i + 1, j)], M[(i, j + 1)]))
            cnt += 1
            if d != (1, 0): bad += 1
out['unimodular_checked'] = cnt; out['unimodular_failures'] = bad
# monodromy trace: product of [[c,-1],[1,0]]
A = [[(1, 0), (0, 0)], [(0, 0), (1, 0)]]
for c in q:
    K = [[c, (-1, 0)], [(1, 0), (0, 0)]]
    A = [[add(mul(A[r][0], K[0][s]), mul(A[r][1], K[1][s])) for s in range(2)] for r in range(2)]
tr = add(A[0][0], A[1][1])
out['monodromy_trace_a_b'] = tr
out['trace_minus_2_sign'] = sign(sub(tr, (2, 0))); out['trace_plus_2_sign'] = sign(add(tr, (2, 0)))
print(json.dumps(out))
