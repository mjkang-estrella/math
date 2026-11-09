"""Verify the source's Theorem 2.3 clumping recurrence against direct simulation,
for the two target maps, on all of S_6. Also verify r/c conjugations.

Recurrence (Theorem 2.3, arXiv:2008.01164v2): let (i1<i2<i3) be the colex-least
index triple with pi[i1]pi[i2]pi[i3] ~= sigma^r for some sigma in T (T^r-occur-
rence); colex-least = min i3, then min i2, then min i1. Then
    s_T(pi) = rev(pi[i2..i3-1]) . s_T(pi minus positions i2..i3-1)
(words over the remaining values; s_T extends to words).
If pi avoids T^r: s_T(pi) = pi^r.
"""
import sys, os, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib_sT import s_T, reverse_word, rev_set

T1 = ((1, 3, 2), (2, 1, 3))
T2 = ((2, 3, 1), (2, 1, 3))

def ranks(els):
    order = sorted(range(len(els)), key=lambda i: els[i])
    r = [0] * len(els)
    for pos, i in enumerate(order):
        r[i] = pos
    return tuple(r)

def contains_occ(w, pats):
    """Return list of index tuples of occurrences of pats in word w."""
    out = []
    m = len(w)
    for pat in pats:
        k = len(pat)
        pr = ranks(pat)
        for idx in itertools.combinations(range(m), k):
            if ranks([w[i] for i in idx]) == pr:
                out.append(idx)
    return out

def colex_least(occs):
    return min(occs, key=lambda t: (t[-1], t[-2], t[-1 - 1]))

def s_T_rec(perm, T):
    """Recursive form of Theorem 2.3."""
    Tr = rev_set(T)
    occs = contains_occ(list(perm), Tr)
    if not occs:
        return reverse_word(tuple(perm))
    i1, i2, i3 = tuple(x + 1 for x in colex_least(occs))  # to 1-based
    block = perm[i2 - 1:i3 - 1]           # positions i2..i3-1 (1-based)
    rest = perm[:i2 - 1] + perm[i3 - 1:]  # a0 a1 a3
    return tuple(reversed(block)) + s_T_rec(rest, T)

ok = True
def run_checks():
    global ok
    for name, T in (("132_213", T1), ("231_213", T2)):
        bad = []
        for pi in itertools.permutations(range(1, 7)):
            if s_T(pi, T) != s_T_rec(pi, T):
                bad.append(pi)
        print(f"recurrence {name}: {'PASS' if not bad else 'FAIL ' + str(bad[:3])}", flush=True)
        ok = ok and not bad

# conjugations: s_{T^r} =? r . s_T . r ; s_{c(T)} =? c . s_T . c
def c_map(T):
    return tuple(tuple(len(t) + 1 - v for v in p) for p in T)

def conj_check(T, conj_w, conj_pat, label):
    Tc = tuple(conj_pat(list(p)) for p in T)
    bad = []
    for pi in itertools.permutations(range(1, 6)):
        lhs = s_T(tuple(conj_w(list(pi))), Tc)
        rhs = tuple(conj_w(list(s_T(pi, T))))
        if lhs != rhs:
            bad.append(pi)
    print(f"conjugation {label}: {'PASS' if not bad else 'FAIL ' + str(bad[:3])}", flush=True)
    return not bad

def r_conj(w):
    return list(reversed(w))

def c_conj(w):
    n = len(w)
    return [n + 1 - v for v in w]

def run_conj():
    global ok
    ok &= conj_check(T1, r_conj, r_conj, "s_{T^r}=r s_T r, T=132_213")
    ok &= conj_check(T1, c_conj, c_conj, "s_{c(T)}=c s_T c, T=132_213")
    ok &= conj_check(T2, r_conj, r_conj, "s_{T^r}=r s_T r, T=231_213")
    ok &= conj_check(T2, c_conj, c_conj, "s_{c(T)}=c s_T c, T=231_213")

if __name__ == "__main__":
    run_checks()
    run_conj()
    with open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                           "work", "recurrence-conjugation-checks.json"), "w") as f:
        json.dump({"all_ok": ok}, f, indent=1)
    print("ALL OK" if ok else "FAILURES PRESENT")
    sys.exit(0 if ok else 1)
