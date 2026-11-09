# Randomised stress test of Lemma W (342364 proof, Section 3): for random R with omega(R) >= w,
# Ttilde(R) - sum_e R_{2e+1} y^e - 2(m+1) R_0  has omega >= w+2.  Also tests single monomials exhaustively.
import sys, json, random
sys.path.insert(0, __import__('os').path.dirname(__file__))
from reduced import Tt, omega
from tcheb import add, v2
random.seed(int(sys.argv[1])); trials = int(sys.argv[2])
def main_part(R, m):
    out = [0]
    for e in range((len(R) + 1) // 2):
        if 2 * e + 1 < len(R) and R[2 * e + 1]:
            out = add(out, [0] * e + [R[2 * e + 1]])
    return add(out, [2 * (m + 1) * R[0]])
fails = []; tested = 0
# exhaustive monomials 2^(w+bitlen(E)) * u * y^E, odd u in {1,3}, m <= 40, E <= 40
for m in range(1, 41):
    for E in range(0, 41):
        for u in (1, 3):
            w = 0; R = [0] * E + [u * 2 ** (w + E.bit_length())]
            H = add(Tt(R, m), main_part(R, m), -1); tested += 1
            if H != [0] and omega(H) < w + 2: fails.append(dict(m=m, E=E, u=u, omegaH=omega(H)))
for t in range(trials):
    m = random.randint(1, 70); L = random.randint(1, 25); w = random.randint(0, 5)
    R = [random.choice([0, 1, -1, 3, 5]) * 2 ** (w + E.bit_length() + random.choice([0, 0, 1])) for E in range(L)]
    if all(c == 0 for c in R): continue
    tested += 1
    T = Tt(R, m); H = add(T, main_part(R, m), -1)
    ok1 = omega(T) >= omega(R) + 1
    ok2 = H == [0] or omega(H) >= omega(R) + 2
    if not (ok1 and ok2): fails.append(dict(m=m, R=R, ok1=ok1, ok2=ok2))
print(json.dumps(dict(tested=tested, fails=len(fails), first=fails[:3])))
