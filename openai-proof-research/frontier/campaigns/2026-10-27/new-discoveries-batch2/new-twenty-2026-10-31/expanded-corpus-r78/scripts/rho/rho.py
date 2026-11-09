# Chapoton-Han arXiv 2001.01449 Sec 5.1: N_0 on palindromic polys of index d:
# (x-1)^2 N_0(P) = (x^d + 1) P(1) - 2 P(x); rho(P) = constant term of last nonzero iterate.
import sys
from math import comb
def N0(P, d):
    # P list of d+1 ints (palindromic index d). return list for index d-2 via exact division
    R = [0]*(d+1); s = sum(P)
    R[0] += s; R[d] += s
    for k,c in enumerate(P): R[k] -= 2*c
    # divide by (x-1)^2 = x^2 - 2x + 1 : synthetic division twice by (x-1)
    for _ in range(2):
        # R(x) = (x-1) Q(x); Q coefficients from top
        Q = [0]*(len(R)-1); acc = 0
        for k in range(len(R)-1, 0, -1):
            acc += R[k]; Q[k-1] = acc
        assert acc + R[0] == 0, 'not divisible'
        R = Q
    assert len(R) == d-1
    return R
def rho(P, d):
    # N0^max on V_d is N0^(floor(d/2)): V_d -> V_0 (d even) or V_1 (d odd); N0 kills V_0 and V_1.
    for _ in range(d//2):
        P = N0(P, d); d -= 2
    return P[0]
def xi1xj(i, j):
    d = 2*i + j; P = [0]*(d+1)
    for k in range(j+1): P[i+k] = comb(j, k)
    return P, d
if __name__ == '__main__':
    # sanity: example from paper
    print('example', rho([1,1,1,1,1], 4))
    print('euler', [rho(*[[c//(2**j) for c in xi1xj(0,2*j)[0]], 2*j]) if True else 0 for j in range(9)])
    M = int(sys.argv[1]); bad = []; checked = 0
    for i in range(M+1):
        for j in range(M+1):
            P, d = xi1xj(i, j); r = rho(P, d); checked += 1
            v = 0; rr = abs(r) if r else 0
            if rr == 0: continue
            while rr % 2 == 0: rr //= 2; v += 1
            if v < j//2: bad.append((i, j, r, v))
    print('checked', checked, 'pairs i,j<=', M, 'violations', bad[:20], len(bad))
    print('M6 row0..', [[rho(*xi1xj(i,j))//2**(j//2) for j in range(6)] for i in range(3)])
