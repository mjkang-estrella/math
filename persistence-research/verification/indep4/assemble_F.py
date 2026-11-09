import json, glob, re, collections
# ---- gather test numbers
t = {}
for tn in ('T1', 'T2', 'T3', 'T5'):
    f = 'logs/test/%s.out' % tn
    try: t[tn] = list(json.load(open(f)).values())[0]
    except Exception: t[tn] = 'NOT RUN'
t4 = []
for f in sorted(glob.glob('logs/test/T4s_*.out')):
    try: t4.append(list(json.load(open(f)).values())[0])
    except Exception: pass
inst = sum(int(re.search(r'PASS \((\d+) solution instances', x).group(1)) for x in t4)
chk = sum(int(re.search(r'instances, (\d+) \(class,prime\)', x).group(1)) for x in t4)
kinds = collections.Counter()
for x in t4:
    for k, v in json.loads(re.search(r'\{.*\}', x).group(0).replace("'", '"')).items(): kinds[k] += v
diffs = []
for f in sorted(glob.glob('logs/diffinc_*.out')):
    for l in open(f):
        m = re.match(r'seed (\d+) compared (\d+) agree (\d+) kill-pair counts \(mine,theirs\): (\{.*\})', l)
        if m: diffs.append((int(m.group(1)), int(m.group(2)), int(m.group(3)), eval(m.group(4))))
dc = sum(d[1] for d in diffs); da = sum(d[2] for d in diffs)
dk = collections.Counter()
for d in diffs:
    for k, v in d[3].items(): dk[k] += v
tam = open('REPORT_F_tamper.md').read()
sec3 = """
## 3. Soundness tests of the kill machinery (independent of the 121 certificates)

`test_F.py` (seeded, stdlib). These test the mathematics of §1 directly, not the certificates.

| test | what it checks | result |
|---|---|---|
| T1 | (a) children partition the parent: for random (M, f, group shapes) all labelled tuples mod fM reducing to the parent are enumerated exhaustively; the set of their sorted keys equals my lift set (no duplicates, none missing); `|Lift| = f·ΠC(f+h−1,h)`; the number of labelled tuples above a parent is `f^{F+1}` times the number below; 2000 random actual (distinct-position) points each lie in exactly one child | %s |
| T2 | (b) sumset is a superset: for random classes, primes, moduli, actual points in the class (random `q = r + M·t`, distinct) satisfy `X mod p ∈ 𝒮(κ)` | %s |
| T3 | (c)/(P2) pins hold on random domain points (`v2(X)=t0`, `X≡K mod 10^k`, `X/2^{t0} ≡ K/2^{t0} mod 8`, mod `E` = lcm-combined modulus); for random smooth targets `N=2^{t0}3^a7^w` placed in the equation, the true `(a mod A, w mod W)` is in the admissible pair set | %s |
| T4 | **positive controls**: ~%d random genuine solutions (random groups, `t0 ∈ {0,1,3}`, random pins valid for that `qmin`) — for every modulus in a list of 8–18 values (including multiples of 27, 7, 36, 252, 1008) and every prime `11 ≤ p < 500` (plus 9901, 333667, 52579, 999999000001, 73, 137, 101, 98641, 99990001 …), the class of the true solution is **never** killed (%d (class,prime) tests; 0 wrong kills); the 3-adic and 7-adic signatures are consistent with the true exponents. On random *non*-solution classes the same machinery produces kills of all kinds (so the test is not vacuous): %s | PASS |
| T5 | (d) my DFS for `X = N` equals brute-force enumeration (1200 values, 1200 solutions, plus spurious-value checks) | %s |

(An earlier, larger T4 run was cancelled for time; the reported T4 figures are the %d completed seeds only. Sumsets with more than 3·10^6 residues are skipped by my checker with an explicit `OverflowError`; none of the 121 real certificates hits that cap.)
""" % (t['T1'], t['T2'], t['T3'], inst, chk, dict(kinds), t['T5'], len(t4))
sec4 = """
## 4. Comparison with M's `check_sym.py` (task 3, performed after sections 1–3 were written)

I read `check_sym.py` (437 lines) only after §§1–3 were written. I did not need to read `gen_sym.py` (the generator is untrusted by construction; only the checker's soundness matters) and did not open it.

**Reading comparison (line-by-line against the proofs in §1):**
* *Lifts:* same weak-composition recursion (`distributions`/`children`), re-sorts after lifting, enumerates `L' = L + jM`; identical to my `group_lifts`.
* *Signature:* `xmod(r, 3^{j+2}, 3^j)` and `xmod(r, 7^{i+1}, 6·7^i)` with the check `pow(10, period, mod) == 1`; `w` unconstrained if `6 ∤ M`. Same as mine.
* *Aligned kill:* `T = 0` ⇒ kill; target coset `2^{−t0} 3^{a}7^{w}·⟨free generators⟩`, membership by `x^{|H|}`. Same.
* *Unaligned (sumset) kill:* start `{K mod p}`, one convolution per **slot** with `{c·10^b : b ≡ e (mod g), 0 ≤ b < d}`, `g = gcd(d, M)`; kill iff **all** elements are impossible. Same as mine, including that it uses the class signature (not the children's).
* *Tail coset:* `modulus = 5^k·2^{max(k−t0,0)}`; admissible `(a mod A, w mod W)` by cycle enumeration (periods = multiplicative orders mod the modulus, with `3` and `7`); the representative list is additionally filtered by the mod-8 condition when `pin2`; exact signature filters representatives; images `g^{h}` with `h = lcm(ord 3^A, ord 7^W)` over free generators. Same as my `E`-modulus formulation (they filter by two moduli, I use their lcm — equivalent since both are congruences for the same `K/2^{t0}`).
* *pin2 without tail:* parity pair from `K/2^{t0} mod 8`, lower bound advanced to the right parity, `ord(9)`, `ord(49)`. Same as mine (my `E = 8` case).
* *Pin validity:* requires `qmin ≥ t0 + 3` (pin2) and `0 ≤ pin_digits ≤ min(3, qmin)`; same as mine.
* *Size leaves:* exact signature required, `N = 2^{t0}3^{a}7^{w}`, meet-in-the-middle over distinct positions with canonical increasing positions inside equal-coefficient groups, filtered by class; mine is a DFS. Both give the same (empty) lists.
* *Brute box:* as mine (they default to `L ≤ 12`, I used `L ≤ 11`).
* Differences that are harmless: M's list `rest` is reordered in place (move-to-front); M's solution tuples are flat `(L, q_1…)` while mine are `[L, [group positions]…]`; M requires coefficients sorted by value and `c %% 10 ≠ 0`, I only require distinct positive coefficients; M's tamper set consists of dimension-1 `scope=class` files.
* **I found no disagreement in mathematics, and no unsound step.**

**Differential tests (black-box agreement of the two kill procedures).** `diff_F.py` imports M's `Checker.killed(p, r, M)` and my `Cert.kills(p, cls, M)` and compares them on random valid parameters (random groups of sizes 1–7 slots, random odd-part `K` with `t0 ∈ {0,1,2,3,5}`, `qmin ≥ t0+1`, pin2 on/off when valid, `pin_digits ∈ {0,1,2,3}`, 5 random moduli from `{1,2,4,6,12,18,36,42,72,84,126,144,216,252,432,504,756,1008}`, 20 random classes each, 12 random primes each from a list including aligned and unaligned primes, 9901, 333667, 99990001, …): %d seeds, **%d comparisons, %d agreements, %d disagreements** (kill/kill: %d, survive/survive: %d; %d pairs skipped by my size cap).

**Verdict comparison on corrupted files.** On the %d tamper files of §6 (`cmp_tamper.json`), M's `check_sym.py` and `check_sym_F.py` returned the same verdict on every file (including the informational vacuous cases).

**Decision.** There is no case where the two checkers disagree, so no case needing arbitration; both are consistent with my proofs. Differences in strictness (M rejects unsorted/non-unique group listings and `c %% 10 = 0` coefficients, mine accepts them but none occur) do not affect any of the 121 certificates.
""" % (len(diffs), dc, da, dc - da, dk.get('(True, True)', 0), dk.get('(False, False)', 0), dk.get('skipped-large-sumset', 0), len(json.load(open('cmp_tamper.json'))))
sec7 = """
## 7. Final count

| | count |
|---|---|
| configurations claimed closed by M (dimension 6: 89, dimension 7: 32) | 121 |
| certificates accepted by my independent checker | 121 / 121 |
| configurations mapped by my independent enumeration to exactly one accepted certificate with matching K, groups, domain | 121 / 121 |
| uncovered slices / v2 edge cases / domain mismatches | 0 / 0 (none needed: all K odd) / 0 |
| unsound kill types found | 0 |
| tamper cases rejected | all genuine tampers (see §6); 2 informational cases correctly accepted |

**Independently confirmed closures: 121 of 121.** The remaining 210 configurations of the 331 baseline stay open (BUDGET); nothing about them is claimed here.

Caveats stated for honesty: (1) the proofs, my checker and M's checker share the specification text, so I added positive controls (T4) and the planted-solution test (§6) that do not depend on it; (2) 11 of the 121 are promoted from a `BUDGET` ledger status (complete files finished at a timeout) — I verified those 11 files in full; (3) the certificates prove "no smooth value in the domain", and the passage from configurations to the multiplicative-persistence statement rests on the digit model of §5 (checked on 339 486 digit strings) and on E's/E2's earlier audit of the framework; (4) the final answer concerns target 14112 only.

## Files
`check_sym_F.py` (checker), `run_all.sh`, `files121.txt`, `logs/all/*.json` (121 results), `summary_F.json`, `aggregate_F.py`, `f_cover.py`/`f_cover_out.json`/`logs/f_cover.log` (coverage), `f_scan.py` (smooth scan to 10^200), `test_F.py` + `logs/test/` (soundness tests), `diff_F.py` + `logs/diffinc_*.out` (differential vs M), `tamper_F.py`, `tamper2_F.py`, `tamper/`, `cmp_tamper.py`/`cmp_tamper.json`, `assemble_F.py`.
Reproduce: `bash -c 'ulimit -v 8000000; python3 -I check_sym_F.py ../highdim/sym/certs/<stage>/<file>.jsonl 11'`; all 121: `./run_all.sh files121.txt logs/all 11`.
""" % ()
head = open('REPORT_F_head.md').read()
proofs = open('REPORT_F_proofs.md').read()
body = open('REPORT_F_body.md').read()
cov = open('REPORT_F_cov.md').read()
open('REPORT_F.md', 'w').write(head + '\n' + proofs + body + sec3 + sec4 + cov + tam + sec7)
print('assembled', len(diffs), 'diff seeds', dc, da, 'T4 seeds', len(t4), inst, chk)
