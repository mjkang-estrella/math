# Independent literal verifier for the refutation of Smyth, arXiv:1512.04084 v1, Conjecture 1.5,
# at (A,a,B,b) = (3,20,2,19). No flow code, no imports from other lane scripts.
# Definitions (literal): U^m_n = {lambda : [m] -> N, sum = n}; concatenation lambda mu;
# lambda dominates mu iff (after non-increasing rearrangement) |lambda|=|mu| and for all j>=1
# sum_{i<=j} lambda_p(i) >= sum_{i<=j} mu_p(i)  (finite lists padded with zeros).
import itertools, json, hashlib, sys
A, a, B, b = 3, 20, 2, 19
G = [(13,12,8,4,2),(13,13,7,3,3),(12,12,8,6,1),(14,12,6,4,3),(13,11,7,7,1),(14,11,6,6,2),(15,11,5,5,3),(16,10,5,4,4)]
def U(m, n):
    return [t for t in itertools.product(range(n+1), repeat=m) if sum(t) == n]
def rearr(t):
    return sorted(t, reverse=True)
def dominates(l, m):
    # l dominates m ; both lists, padded with zeros to a common length
    L = max(len(l), len(m)); p = rearr(l) + [0]*(L-len(l)); q = rearr(m) + [0]*(L-len(m))
    if sum(p) != sum(q): return False
    sp = sq = 0
    for j in range(L):
        sp += p[j]; sq += q[j]
        if sp < sq: return False
    return True
X = [(l, m) for l in U(A, b) for m in U(B, a)]
Y = [(l, m) for l in U(A, a) for m in U(B, b)]
assert len(X) == 210*21 == 4410 and len(Y) == 231*20 == 4620
for g in G: assert sum(g) == a+b == 39 and list(g) == rearr(g)
inD = lambda t: any(dominates(g, t) for g in G)
S = [x for x in X if inD(x[0]+x[1])]
T = [y for y in Y if inD(y[0]+y[1])]
# Closure check (redundant with transitivity, done explicitly on rearranged types):
Stypes = {tuple(rearr(x[0]+x[1])) for x in S}
Ytypes = {tuple(rearr(y[0]+y[1])) for y in Y}
Ttypes = {tuple(rearr(y[0]+y[1])) for y in T}
bad = [(p, q) for p in Stypes for q in Ytypes if dominates(p, q) and q not in Ttypes]
out = {'A':A,'a':a,'B':B,'b':b,'|X|':len(X),'|Y|':len(Y),'generators':G,'|S|':len(S),'|T|':len(T),
       'S_types':len(Stypes),'closure_violations':len(bad),
       'S_sha256':hashlib.sha256(json.dumps(sorted(S)).encode()).hexdigest(),
       'T_sha256':hashlib.sha256(json.dumps(sorted(T)).encode()).hexdigest()}
print(json.dumps(out, indent=1))
assert len(S) == 1137 and len(T) == 1134 and not bad
print('CERTIFICATE OK: any map gamma with lambda1mu1 dominating gamma(.) sends S into T, |S| > |T|, so gamma is not injective.')
