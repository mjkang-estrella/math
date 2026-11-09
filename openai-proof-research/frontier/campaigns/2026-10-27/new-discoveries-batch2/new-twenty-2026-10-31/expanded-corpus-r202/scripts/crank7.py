"""349529: compare both sides of Bandyopadhyay Conjecture 5.1 (arXiv:2101.10910) as power series to q^N.
A..E exactly as defined in the source (lines 474-476). usage: crank7.py N"""
import sys
N = int(sys.argv[1])

def mul(a, b):
    c = [0] * (N + 1)
    for i, x in enumerate(a):
        if x:
            for j in range(0, N + 1 - i):
                if b[j]: c[i + j] += x * b[j]
    return c

def inv_factor(e, a):  # multiply a by 1/(1-q^e)
    a = a[:]
    for i in range(e, N + 1): a[i] += a[i - e]
    return a

def factor(e, a):  # multiply a by (1-q^e)
    a = a[:]
    for i in range(N, e - 1, -1): a[i] -= a[i - e]
    return a

def prod(num_res, den_res, mod):  # prod over residues r (mod `mod`) of (q^r;q^mod)_inf factors
    a = [1] + [0] * N
    for r in den_res:
        e = r
        while e <= N: a = inv_factor(e, a); e += mod
    for r in num_res:
        e = r
        while e <= N: a = factor(e, a); e += mod
    return a

one = [1] + [0] * N
# LHS
S = [0] * (N + 1)
n = 1
while n * (n + 1) // 2 <= N:
    t = [0] * (N + 1); t[n * (n + 1) // 2] = (-1) ** n
    for _ in range(5): t = factor(n, t)
    t2 = t[:]
    for i in range(N, n - 1, -1): t2[i] += t[i - n]   # times (1+q^n)
    t2 = inv_factor(7 * n, t2)
    S = [x + y for x, y in zip(S, t2)]
    n += 1
invq = prod([], list(range(1, 2)), 1)  # 1/(q;q)
LHS = mul(invq, S)
A = prod([49], [7, 42], 49)
B = prod([14, 35, 49], [7, 21, 28, 42], 49)
C = prod([49], [14, 35], 49)
D = prod([49], [21, 28], 49)
E = prod([7, 42, 49], [14, 21, 28, 35], 49)
def sh(a, s, c): return [0] * s + [c * x for x in a[:N + 1 - s]]
RHS = [sum(v) for v in zip(sh(A, 1, -1), sh(B, 2, 3), sh(C, 3, -2), sh(D, 4, 1), sh(E, 6, -3))]
diff = [i for i in range(N + 1) if LHS[i] != RHS[i]]
print('N', N, 'mismatches', len(diff), 'first', diff[:10])
print('LHS[:20]', LHS[:20]); print('RHS[:20]', RHS[:20])
mod7 = [i for i in range(N + 1) if (LHS[i] - RHS[i]) % 7]
print('mismatches mod 7:', len(mod7), mod7[:10])
