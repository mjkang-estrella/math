#!/usr/bin/env python3
"""critic_G_checks.py — hostile independent verification of notes/pure_math.md.

Reviewer G. Re-derives everything from scratch; imports ONLY persistence.py
(len23_table, persistence) as the read-only reference DP.
Sections: A (zero-trap), B (tau cascade + deficits), C (case table),
          C5 (min-lex DFS up to a<=240,b<=160), Fonga (§6).
"""
import sys, math, time, itertools
from fractions import Fraction

sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/persistence-research/src')
from persistence import persistence, len23_table

def hdr(t): print("\n" + "=" * 72 + f"\n{t}\n" + "=" * 72)

# =====================================================================
hdr("THEOREM A: 10 | m  <=>  a>=1 and c>=1, for m = 2^a 3^b 5^c 7^d")
# =====================================================================
bad = []
for a in range(5):
    for b in range(4):
        for c in range(5):
            for d in range(4):
                m = 2**a * 3**b * 5**c * 7**d
                # verify v2 = a, v5 = c directly
                x, v2 = m, 0
                while x % 2 == 0: x //= 2; v2 += 1
                x, v5 = m, 0
                while x % 5 == 0: x //= 5; v5 += 1
                assert v2 == a and v5 == c, (a,b,c,d)
                if (m % 10 == 0) != (a >= 1 and c >= 1):
                    bad.append((a,b,c,d,m))
print("v2==a and v5==c for all tested (a,b,c,d): OK")
print("10|m <=> (a>=1 and c>=1) counterexamples:", bad if bad else "NONE")

# 10|m => Pi(m)=0 => P(m)=1 ; and P(m)>=2 => a*c=0 (7-smooth m)
viol = []
def gen7smooth(bound):
    out = []
    a = 0
    while 2**a < bound:
        b = 0
        while 2**a * 3**b < bound:
            c = 0
            while 2**a * 3**b * 5**c < bound:
                d = 0
                while 2**a * 3**b * 5**c * 7**d < bound:
                    out.append((a, b, c, d, 2**a * 3**b * 5**c * 7**d))
                    d += 1
                c += 1
            b += 1
        a += 1
    return out
for (a,b,c,d,m) in gen7smooth(10**6):
    if m % 10 == 0:
        assert persistence(m) == 1
    elif persistence(m) >= 2 and a >= 1 and c >= 1:
        viol.append(m)
print("P(m)>=2 with a>=1,c>=1 (should be none):", viol if viol else "NONE")
print("NOTE: 'lies in exactly one of two families' fails for a=c=0 (m=3^b 7^d in both).")

# =====================================================================
hdr("THEOREM B / §3: independent tau-table by full lattice sweep below tau10")
# =====================================================================
T10_CLAIM = 4996238671872
T9_CLAIM  = 438939648
pts = gen7smooth(T10_CLAIM)          # all 7-smooth m < claimed tau10
print("lattice points strictly below 2^19*3^4*7^6:", len(pts), "(pure_math §3 says ~12,700)")
pmax, argmax = 0, None
Pof = {}
for (a,b,c,d,m) in pts:
    p = persistence(m)
    Pof[m] = p
    if p > pmax: pmax, argmax = p, m
print("max P(m) over all 7-smooth m < tau10:", pmax, "at", argmax, "=> tau10 minimal iff pmax==9")
taus = {}
for k in range(1, 10):
    cand = [m for (a,b,c,d,m) in pts if Pof[m] >= k]
    taus[k] = min(cand) if cand else None
# tau_10: verified separately: P(claim)=10 and max P below claim is 9 (pmax above)
assert pmax == 9 and persistence(T10_CLAIM) == 10
taus[10] = T10_CLAIM
for k in sorted(taus): print(f"  tau_{k} = {taus[k]}")
print("tau_10 == 4996238671872 :", taus[10] == T10_CLAIM,
      " (minimality: max P below it = %d at %d)" % (pmax, argmax))
print("tau_9  == 438939648    :", taus[9] == T9_CLAIM)
print("P(4996238671872) =", persistence(T10_CLAIM), " (must be 10)")
print("P(438939648)     =", persistence(T9_CLAIM),  " (must be 9)")
print("2^19*3^4*7^6 =", 2**19 * 3**4 * 7**6)
print("2^4*3^20*7^5 =", 2**4 * 3**20 * 7**5)
print("Pi(937638166841712) =", persistence.__globals__['digit_product'](937638166841712))

# record chain sanity
n = 277777788888899
chain = [n]
while n >= 10:
    n = int(''.join(sorted(str(n)))) and 0 or 0  # placeholder, real chain below
chain = [277777788888899]
x = 277777788888899
while x >= 10:
    x = math.prod(map(int, str(x)))
    chain.append(x)
print("record chain:", chain)
print("P(277777788888899) =", persistence(277777788888899), "(must be 11)")
print("Pi(277777788888899) = 2^19*3^4*7^6 :", math.prod(map(int, str(277777788888899))) == 2**19*3**4*7**6)

# =====================================================================
hdr("THEOREM B: index check and the corrected cascade")
# =====================================================================
# (B1): m_{i+1} = Pi(m_i) <= 9^{dc(m_i)}  and  m_{i+1} >= tau_{10-i}
#   => dc(m_i) >= ceil(log9 tau_{10-i}).  Document's example says "dc(m_1) >= ceil(log9 tau_10) = 14".
print("9^13 =", 9**13, " < tau_10 =", T10_CLAIM, ":", 9**13 < T10_CLAIM)
print("9^14 =", 9**14, " > tau_10 :", 9**14 > T10_CLAIM)
print("ceil(log9 tau_10) =", math.ceil(math.log(T10_CLAIM, 9)))
for i in range(0, 10):
    tk = taus[10 - i]
    print(f"  i={i}:  dc(m_{i}) >= ceil(log9 tau_{10-i}) = ceil(log9 {tk}) = {math.ceil(math.log(tk, 9))}")
print("=> document's 'dc(m_1) >= 14' is WRONG as labelled; the i=0 bound reads dc(m_0) >= 14.")
print("   Correct i=1 bound: dc(m_1) >= ceil(log9 tau_9) =", math.ceil(math.log(T9_CLAIM, 9)))
# magnitude route for m_1: m_1 >= tau_10 only gives dc(m_1) >= 13
print("   (magnitude route m_1>=tau_10 gives only dc(m_1)>=13; product route gives 10)")

# =====================================================================
hdr("THEOREM B/(B2): deficit arithmetic at D=14")
# =====================================================================
val = 14 * T10_CLAIM ** (1 / 14)
print(f"14 * tau_10^(1/14) = {val!r}")
import decimal
decimal.getcontext().prec = 30
vald = decimal.Decimal(14) * (decimal.Decimal(T10_CLAIM) ** (decimal.Decimal(1) / 14))
print("high precision:", vald)
print("=> s(m_0) >= 114 (integer), max 14-digit digit sum = 126, deficit <= 12")
print("9^12 =", 9**12, " < tau_10 :", 9**12 < T10_CLAIM)
print("seven 7s  => deficit 14 > 12 : excluded by deficit alone :", 7*2 > 12)
print("five 6s   => deficit 15 > 12 : excluded by deficit alone :", 5*3 > 12)
print("three 4s  => deficit 15 > 12 : excluded by deficit alone :", 3*5 > 12)
print("two 3s    => deficit 12 <= 12: NOT excluded by deficit alone!", 2*6 <= 12)
print("   {3,3,9^12}: deficit 12, but digit product 9^12 = %d < tau_10 -> excluded" % 9**12,
      "ONLY by the product constraint Pi(m_0)=m_1>=tau_10.")
# exhaustive: all 14-digit profiles with deficit<=12 containing two digits <=3
prof = []
for t in range(0, 13):
    pass
cnt = 0
for n3 in range(0, 3):
    for n2 in range(0, 2):
        for n1 in range(0, 2):
            for n0 in range(0, 2):
                d = 6*n3 + 7*n2 + 8*n1 + 9*n0
                if d <= 12 and (n3 + n2 + n1 + n0) >= 2:
                    cnt += 1
                    prof.append((n3, n2, n1, n0, d))
print("profiles with >=2 digits <=3 and deficit<=12:", prof, "(only (2,0,0,0)={3,3} has deficit<=12)")

# =====================================================================
hdr("THEOREM C.2: closed-form table vs len23 DP, a<=60 b<=40")
# =====================================================================
VEC = {2: (1, 0), 3: (0, 1), 4: (2, 0), 6: (1, 1), 8: (3, 0), 9: (0, 2)}

def F_closed(a, b):
    m3, m2 = a % 3, b % 2
    if   (m3, m2) == (0, 0): return [8]*(a//3) + [9]*(b//2)
    elif (m3, m2) == (1, 0): return [2] + [8]*((a-1)//3) + [9]*(b//2)
    elif (m3, m2) == (2, 0): return [4] + [8]*((a-2)//3) + [9]*(b//2)
    elif (m3, m2) == (0, 1): return [3] + [8]*(a//3) + [9]*((b-1)//2)
    elif (m3, m2) == (1, 1): return [6] + [8]*((a-1)//3) + [9]*((b-1)//2)
    else:                    return [2, 6] + [8]*((a-2)//3) + [9]*((b-1)//2)

MAXA, MAXB = 60, 40
t23 = len23_table(MAXA + 3, MAXB + 2)
prod_bad, len_bad, lp_bad = [], [], []
for a in range(MAXA + 1):
    for b in range(MAXB + 1):
        F = F_closed(a, b)
        p = math.prod(F) if F else 1
        if p != 2**a * 3**b: prod_bad.append((a, b, F))
        if len(F) != t23[a][b]: len_bad.append((a, b, len(F), t23[a][b]))
        if t23[a][b] != (2*a + 3*b + 5) // 6: lp_bad.append((a, b, t23[a][b]))
print("product mismatches:", prod_bad if prod_bad else "NONE")
print("length-vs-DP mismatches:", len_bad if len_bad else "NONE")
print("len23 == ceil(a/3+b/2) violations (LP bound not tight):", lp_bad if lp_bad else "NONE")

# =====================================================================
hdr("THEOREM C.2(iii): FULL brute force, a<=12 b<=8 — every factorization")
# =====================================================================
def all_factorizations(a, b):
    """All nondecreasing digit sequences (multisets) with product 2^a 3^b."""
    res = []
    def rec(ra, rb, mind, seq):
        if ra == 0 and rb == 0:
            res.append(tuple(seq)); return
        for d in range(mind, 10):
            if d in (5, 7): continue
            da, db = VEC[d]
            if da <= ra and db <= rb:
                rec(ra - da, rb - db, d, seq + [d])
    rec(a, b, 2, [])
    return res

mismatch = []
for a in range(13):
    for b in range(9):
        facs = all_factorizations(a, b)
        L = min(len(f) for f in facs) if (a or b) else 0
        if (a or b) and L != t23[a][b]:
            mismatch.append(("MINLEN", a, b, L, t23[a][b]))
        mins = sorted(f for f in facs if len(f) == L)
        lexmin = mins[0] if mins else ()
        Fc = tuple(F_closed(a, b))
        if lexmin != Fc:
            mismatch.append(("LEX", a, b, "brute:", lexmin, "table:", Fc,
                             "same length set:", [f for f in facs if len(f) == L]))
print("brute-force mismatches over a<=12,b<=8 (117 pairs):",
      mismatch if mismatch else "NONE — table is min-length AND min-lex everywhere tested")

# targeted probes from the brief
for (a, b) in [(2, 1), (7, 0), (5, 1), (4, 1), (1, 1), (2, 0), (1, 0), (0, 1), (19, 4)]:
    facs = all_factorizations(a, b) if (a or b) else [()]
    L = min(len(f) for f in facs)
    mins = sorted(f for f in facs if len(f) == L)
    print(f"  (a,b)=({a},{b}): 2^a*3^b={2**a*3**b}, len23={t23[a][b]}, brute minlen={L},")
    print(f"     all min-length multisets: {mins}")
    print(f"     lex-min = {mins[0]}   table F = {tuple(F_closed(a,b))}   match: {mins[0]==tuple(F_closed(a,b))}")

# =====================================================================
hdr("THEOREM C.2: independent min-lex DFS with exact pruning, a<=240 b<=160")
# =====================================================================
def lexmin_dfs(a, b, t):
    """Lex-smallest nondecreasing sequence of exactly t[a][b] digits, product 2^a 3^b.
       Pruning is exact: no completion of length r exists if len23(ra,rb) > r or ra+rb < r."""
    L = t[a][b]
    sys.setrecursionlimit(10000)
    def dfs(ra, rb, r, last):
        if r == 0:
            return [] if (ra == 0 and rb == 0) else None
        if t[ra][rb] > r or ra + rb < r:
            return None
        for d in range(max(last, 2), 10):
            if d in (5, 7): continue
            da, db = VEC[d]
            if da <= ra and db <= rb:
                sub = dfs(ra - da, rb - db, r - 1, d)
                if sub is not None:
                    return [d] + sub
        return None
    return dfs(a, b, L, 2)

t_big = len23_table(243, 162)
t0 = time.time()
bad_lex = []
checked = 0
for a in range(0, 241):
    for b in range(0, 161):
        got = tuple(lexmin_dfs(a, b, t_big))
        want = tuple(F_closed(a, b))
        checked += 1
        if got != want:
            bad_lex.append((a, b, got, want))
        if a % 80 == 40 and b == 80:
            print(f"  ...progress a={a}, {time.time()-t0:.1f}s")
print(f"checked {checked} pairs in {time.time()-t0:.1f}s")
print("DFS lex-min mismatches vs closed form:", bad_lex if bad_lex else "NONE (0/%d)" % checked)

# =====================================================================
hdr("THEOREM C.2(d): record-setter consistency")
# =====================================================================
F194 = F_closed(19, 4)
digits = sorted([2] + [7]*6 + [8]*6 + [9]*2)
print("F(19,4) =", F194, " (a=19≡1 mod 3, b=4≡0 mod 2)")
print("sorted digits of 277777788888899:", sorted(map(int, str(277777788888899))))
print("match:", sorted(F194 + [7]*6) == sorted(map(int, str(277777788888899))))
print("len(m_0)=6+len23(19,4) =", 6 + t_big[19][4], "= number of digits of the record holder:",
      6 + t_big[19][4] == len(str(277777788888899)))

# =====================================================================
hdr("THEOREM C.3: five family brute check")
# =====================================================================
def F5(b, c, d):
    return [3]*(b % 2) + [5]*c + [7]*d + [9]*(b//2)
bad5 = []
for b in range(0, 9):
    for c in range(0, 5):
        for d in range(0, 5):
            m = 3**b * 5**c * 7**d
            # brute: all digit multisets with product m
            res = []
            def rec(rem, mind, seq):
                if rem == 1:
                    res.append(tuple(seq)); return
                for dg in range(mind, 10):
                    if rem % dg == 0:
                        rec(rem // dg, dg, seq + [dg])
            rec(m, 2, [])
            L = min(len(f) for f in res)
            lexmin = sorted(f for f in res if len(f) == L)[0]
            if lexmin != tuple(sorted(F5(b, c, d))):
                bad5.append((b, c, d, lexmin, tuple(sorted(F5(b, c, d)))))
print("five-family mismatches (b<=8,c<=4,d<=4):", bad5 if bad5 else "NONE")

# =====================================================================
hdr("§6 FONGA: family {4,4,7}+1^j — max v2, all arrangements, j<=40 (and 60)")
# =====================================================================
def v2(n): return (n & -n).bit_length() - 1
best = (0, None)
for j in range(0, 61):
    slots = j + 3
    for p4 in itertools.combinations(range(slots), 2):
        rest = [s for s in range(slots) if s not in p4]
        for p7 in rest:
            digs = ['1'] * slots
            digs[p4[0]] = digs[p4[1]] = '4'
            digs[p7] = '7'
            n = int(''.join(digs))
            v = v2(n)
            if v > best[0]:
                best = (v, n, j)
print("max v2 over all arrangements j<=60:", best)
print("111744 = 2^7*3^2*97 :", 111744 == 2**7 * 3**2 * 97, " v2(111744) =", v2(111744))
print("Fonga/doc claim 'max v2 = 7 at 111744':", "CONFIRMED (j<=60)" if best[0] == 7 and best[1] == 111744 else "VIOLATED: %r" % (best,))

# complete infinite-family check: v2(n)>=8 <=> 256 | n <=> last-8-digit suffix S == 0 mod 256
# (for n with >=8 digits; smaller n enumerated directly above)
def suffix_bad_exists(max_ones):
    """any 8-digit suffix over {1,4,7} with <=2 fours, <=1 seven, ones<=max_ones, S%256==0?"""
    hits = []
    for i in range(0, 3):          # fours
        for t in range(0, 2):      # sevens
            s = 8 - i - t          # ones
            if s > max_ones: continue
            for pos4 in itertools.combinations(range(8), i):
                rem = [x for x in range(8) if x not in pos4]
                for pos7 in itertools.combinations(rem, t):
                    dg = ['1'] * 8
                    for p in pos4: dg[p] = '4'
                    for p in pos7: dg[p] = '7'
                    S = int(''.join(dg))
                    if S % 256 == 0:
                        hits.append(S)
    return hits
allhits = []
for j in range(5, 200):
    allhits += [(j, S) for S in suffix_bad_exists(j)]
print("8-digit suffixes S (sub-multiset of {4,4,7,1^j}, j>=5) with 256|S :",
      allhits if allhits else "NONE for any j => v2<=7 for the ENTIRE family (complete proof)")
# also direct: no family member with <=7 digits divisible by 256
small_bad = []
for j in range(0, 5):
    slots = j + 3
    for p4 in itertools.combinations(range(slots), 2):
        rest = [s for s in range(slots) if s not in p4]
        for p7 in rest:
            digs = ['1'] * slots
            digs[p4[0]] = digs[p4[1]] = '4'
            digs[p7] = '7'
            n = int(''.join(digs))
            if n % 256 == 0: small_bad.append(n)
print("family members with <=7 digits divisible by 256:", small_bad if small_bad else "NONE")

print("\nALL CHECKS COMPLETE")
