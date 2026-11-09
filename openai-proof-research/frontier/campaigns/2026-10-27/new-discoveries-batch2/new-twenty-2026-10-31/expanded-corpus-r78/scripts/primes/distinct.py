# Fang-Chen Conjecture 1 (arXiv 1110.4714): for s>=3 every l > p_2+...+p_{s+2} is a sum of
# exactly s distinct primes. Exact DP with Python-int bitsets: R[k] = set of sums of k distinct primes.
import sys, json
S = int(sys.argv[1]); MARGIN = int(sys.argv[2])
def primes_upto(N):
    b = bytearray([1])*(N+1); b[0]=b[1]=0
    for i in range(2, int(N**0.5)+1):
        if b[i]: b[i*i::i] = bytearray(len(b[i*i::i]))
    return [i for i in range(N+1) if b[i]]
P = primes_upto(200000)
T = {s: sum(P[1:s+2]) for s in range(3, S+1)}  # p_2..p_{s+2} = P[1..s+1]
LMAX = max(T.values()) + MARGIN
mask = (1 << (LMAX+1)) - 1
R = [0]*(S+1); R[0] = 1
for p in P:
    if p > LMAX: break
    for k in range(S, 0, -1):
        R[k] |= (R[k-1] << p) & mask
fails = {}
for s in range(3, S+1):
    lo, hi = T[s]+1, T[s]+MARGIN
    bad = [l for l in range(lo, hi+1) if not (R[s] >> l) & 1]
    if bad: fails[s] = bad[:10]
    # also confirm sharpness: is T[s] itself non-representable?
print(json.dumps({'s_range': [3, S], 'margin': MARGIN, 'LMAX': LMAX, 'fails': fails,
                  'threshold_nonrep': [s for s in range(3, S+1) if not (R[s] >> T[s]) & 1][:20]}))
