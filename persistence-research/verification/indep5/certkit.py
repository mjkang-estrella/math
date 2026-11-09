"""[F5] Builders for synthetic nd-sym certificates used by test_F5.py / tamper_F5.py.
Stdlib only.  Writes only inside verification/indep5/."""
import json, os, random, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_sym_F5 as F5

def write_cert(path, meta, nodes):
    with open(path, 'w') as f:
        f.write(json.dumps(meta) + '\n')
        for n in nodes:
            f.write(json.dumps(n) + '\n')
    return path

def make_meta(groups, K, qmin, k=0, pin2=False):
    """groups: list of [coef, mult]; dim = 1 + sum(mult); root all-zero mod 1."""
    return {"k": "meta", "format": "nd-sym", "version": 1, "domain": "unordered",
            "scope": "full", "groups": [list(g) for g in groups], "K": K, "qmin": qmin,
            "dim": 1 + sum(m for _, m in groups), "pin2": bool(pin2),
            **({"pin_digits": k} if k else {}),
            "root": {"r": [0] + [[0] * m for _, m in groups], "m": 1}}

def root_node_for(meta, m2, rest):
    return {"id": 0, "p": -1, "m": 1, "r": meta["root"]["r"], "k": "i", "m2": m2,
            "c": [], "rest": list(rest)}

def classes_mod(M, groups):
    """All class tuples mod M with root shape: (L mod M, tuple(sorted residues) per group)."""
    import itertools
    per = []
    for c, m in groups:
        per.append(itertools.combinations_with_replacement(range(M), m))
    out = []
    for L in range(M):
        for combo in itertools.product(*per):
            out.append((L,) + tuple(tuple(sorted(x)) for x in combo))
    return out

def find_killing_primes(ct, clses, M, pmax=60000, maxset=512):
    """Greedy: find a small set of primes such that every class in `clses` is killed
    by at least one of them (using F5's own kill machinery).  Returns list or None.
    Primes whose decimal period d = ord_p(10) has d/gcd(d,M) > maxset are skipped
    (their sumset convolution would be expensive)."""
    rest = []
    alive = set(clses)
    for p in _primes(pmax):
        if p <= 7: continue
        if not alive: break
        d = F5.order(10, p); g = F5.gcd(d, M)
        if d // g > maxset: continue
        killed = []
        for cls in sorted(alive):
            try:
                ok = ct.kills(p, cls, M)[0]
            except OverflowError:
                ok = False          # sumset too large for this prime: skip it
            if ok: killed.append(cls)
        if killed:
            rest.append(p)
            alive.difference_update(killed)
    return rest if not alive else None

def _primes(pmax):
    sieve = bytearray([1]) * (pmax + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, int(pmax ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = b'\x00' * len(sieve[i * i::i])
    return [i for i in range(pmax + 1) if sieve[i]]

def run_check(path, brute=11):
    """In-process F5 check; returns the result dict (result/problems/...)."""
    import io, contextlib
    sys.stdout = io.StringIO()
    try:
        ct, claimed, brute_pts = F5.check(path, brute)
        res = dict(result='FAIL' if ct.problems else 'PASS', problems=list(ct.problems[:10]),
                   stats=dict(ct.stats), kinds=dict(ct.kinds), ukinds=dict(ct.ukinds),
                   claimed=claimed, brute=brute_pts)
    except Exception as e:
        res = dict(result='FAIL', problems=['exception %s: %s' % (type(e).__name__, e)])
    finally:
        sys.stdout = sys.__stdout__
    return res

def check_with_patched(path, patch, brute=11):
    """Run F5.check with F5.Cert temporarily replaced by `patch` (a subclass)."""
    old = F5.Cert
    F5.Cert = patch
    try:
        return run_check(path, brute)
    finally:
        F5.Cert = old

def brute_smooth_points(groups, K, qmin, t0, Lmax):
    """Independent enumeration of all smooth domain points with L <= Lmax."""
    import itertools
    out = []
    F = sum(m for _, m in groups)
    coefs = [c for c, _ in groups]
    for L in range(qmin + (1 if F else 0), Lmax + 1):
        pos = list(range(qmin, L))
        if len(pos) < F: continue
        def rec(gi, avail, acc):
            if gi == len(coefs):
                yield list(acc); return
            for sub in itertools.combinations(avail, groups[gi][1]):
                yield from rec(gi + 1, [x for x in avail if x not in sub], acc + [list(sub)])
        for grps in rec(0, pos, []):
            X = 10 ** L + K + sum(c * 10 ** q for c, g in zip(coefs, grps) for q in g)
            if X % (1 << t0): continue
            Y = X >> t0
            if Y % 2 == 0: continue
            for pr in (3, 7):
                while Y % pr == 0: Y //= pr
            if Y == 1: out.append([L] + [q for g in grps for q in sorted(g)])
    return sorted(out)
