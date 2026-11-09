# Find 0/1 bridge matrices W (b x r) with all relevant minors = +-1 over Z:
#  (A) top-left jxj (rows 0..j-1, cols 0..j-1), j=1..r
#  (B) rows s..s+r-1 (all r cols), s=0..b-r
#  (C) bottom-right jxj (rows b-j..b-1, cols r-j..r-1), j=1..r
# Then the cyclic sequence e_0..e_{b-1} (repeated m>=1 times) followed by the columns of W has every
# b cyclically consecutive vectors forming a basis over EVERY field.
import sys, itertools, random, json
from fractions import Fraction
def det(M):
    M = [[Fraction(x) for x in row] for row in M]; n = len(M); d = Fraction(1)
    for i in range(n):
        p = next((r for r in range(i, n) if M[r][i] != 0), None)
        if p is None: return 0
        if p != i: M[i], M[p] = M[p], M[i]; d = -d
        d *= M[i][i]
        for r in range(i+1, n):
            f = M[r][i] / M[i][i]
            if f: M[r] = [a - f*b for a, b in zip(M[r], M[i])]
    return d
def ok(W, b, r):
    for j in range(1, r+1):
        if abs(det([W[i][:j] for i in range(j)])) != 1: return False
        if abs(det([W[i][r-j:] for i in range(b-j, b)])) != 1: return False
    for s in range(0, b-r+1):
        if abs(det([W[i] for i in range(s, s+r)])) != 1: return False
    return True
if __name__ == "__main__":
    random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    B = int(sys.argv[1])
    for b in range(2, B+1):
        for r in range(1, b):
            found = None
            for t in range(200000):
                W = [[1 if random.random() < 0.35 else 0 for _ in range(r)] for _ in range(b)]
                if ok(W, b, r): found = W; break
            print(json.dumps({'b': b, 'r': r, 'W': found}), flush=True)
