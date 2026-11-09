# Sign-class averaging test (Stylianou-type) for the 8-player subspace profile.
# Voter described by signed agreements e_{f,b} (f in 1..7, b in {0,1}: b=1 <-> the deviation support).
# Code point a in F_2^3 has value A(a) = sum_f chi_f(a) (e_{f0}+e_{f1}); deviator (replacing 0) has
# value Bv = sum_f (e_{f0} - e_{f1}); larger value = closer.  For a magnitude pattern alpha, average the
# deviator's tie-split share over all sign choices of nonzero entries; "good" iff average <= 1/8.
import sys; sys.path.insert(0, 'scripts')
from vk import np, fval
from fractions import Fraction
import itertools, random
CHI = np.array([[1 - 2 * fval(f, a) for f in range(1, 8)] for a in range(8)], dtype=np.int64)  # 8x7
SIGNS = np.array(list(itertools.product([1, -1], repeat=14)), dtype=np.int64)  # 16384 x 14
def avg_share(alpha):
    """alpha: length-14 array, index 2*(f-1)+b. returns exact Fraction average share."""
    al = np.asarray(alpha, dtype=np.int64)
    nz = np.flatnonzero(al)
    # restrict sign enumeration to nonzero coordinates: take rows of SIGNS where zero coords are +1
    mask = np.all(SIGNS[:, [i for i in range(14) if al[i] == 0]] == 1, axis=1) if len(nz) < 14 else np.ones(len(SIGNS), bool)
    E = SIGNS[mask] * al  # rows: signed e
    e0 = E[:, 0::2]; e1 = E[:, 1::2]
    A = (e0 + e1) @ CHI.T           # rows x 8
    Bv = (e0 - e1).sum(axis=1)
    Aot = A[:, 1:]
    mx = Aot.max(axis=1)
    win = Bv >= mx
    ties = (Aot == Bv[:, None]).sum(axis=1)
    num = sum(Fraction(int(c), k + 1) for k, c in zip(*np.unique(ties[win], return_counts=True)))
    return num / int(mask.sum())
if __name__ == '__main__':
    # sanity: with e_{f1}=0 for all f the deviator is the original player 0: average must be exactly 1/8
    random.seed(0)
    for _ in range(20):
        al = [random.randint(0, 4) if b == 0 else 0 for f in range(7) for b in range(2)]
        assert avg_share(al) == Fraction(1, 8), al
    print('sanity ok (c=0 patterns average exactly 1/8)')
    mode = sys.argv[1]
    par = [int(ch) for ch in sys.argv[2]]  # parity of m_f, f=1..7
    K = int(sys.argv[3]); trials = int(sys.argv[4])
    bad = []; worst = Fraction(0)
    def gen():
        if mode == 'exh':
            for tup in itertools.product(range(K + 1), repeat=7):
                # tup gives alpha_{f1}; alpha_{f0} chosen minimal with right parity, then small variants
                yield tup
        else:
            for _ in range(trials):
                yield tuple(random.randint(0, K) for _ in range(7))
    cnt = 0
    for a1 in gen():
        for _ in range(1 if mode == 'exh' else 1):
            a0 = [random.randint(0, K) for _ in range(7)]
            a0 = [x if (x + y) % 2 == par[i] else x + 1 for i, (x, y) in enumerate(zip(a0, a1))]
            al = [v for f in range(7) for v in (a0[f], a1[f])]
            s = avg_share(al); cnt += 1
            if s > worst: worst = s
            if s > Fraction(1, 8):
                bad.append((al, s))
    print('parity', par, 'K', K, 'tested', cnt, 'bad', len(bad), 'worst avg', worst, float(worst * 8))
    for al, s in sorted(bad, key=lambda z: -z[1])[:15]:
        print('  BAD alpha (f0,f1 pairs)', [(al[2*i], al[2*i+1]) for i in range(7)], 'avg', s, float(s * 8))
