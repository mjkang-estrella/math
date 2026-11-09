# SUMMARY — MathDB 375237, Ward/Moriwaki three-parameter Subtraction Nim period conjecture (lane pi-subtraction-nim-source-hypothesis-r325)

**Disposition: PARK (hypothesis refuted as worded; literal conjecture survives; no full-scope proof route within caps). No PROOF.md. No substantive claim.**

## 1. Exact target

MathDB record **375237**, "Period conjecture for three-parameter Subtraction Nim", post type conjecture, status open, no solutions (cached record: `campaigns/2026-10-25/twenty-proof-discrete-lane/sources/mathdb-375237.json`, sha256 `c33184738c2da70900f5ffdd7dc11e0e984d0b3acff9987a61c9f4bf677dfbbd`, 1781 bytes). Cached statement:

> "Let $G(S)$ be the normal-play Subtraction Nim game with move set $S=\{a,b,c\}$, where $0<a<b<c$ and $c\ne a+b$. Its Nim value function is considered as a function of the heap or string length. **Period conjecture.** The Nim value function is periodic with a period equal to one of $a+b$, $b+c$, or $c+a$."

## 2. Primary sources actually read (full bodies, retained bytes)

- **Ward, "A conjecture about periods in subtraction games", arXiv:1606.04029v1 (2016)** — original conjecture, 2 pp. Conjecture 1, Case II (s3 ≠ s1+s2): the (minimal) period p "is a divisor of at least one of the numbers s_i + s_j … and moreover, the period p is exactly the gcd of all such terms, i.e. p = gcd_{(i,j)∈G}(s_i+s_j)". Ward: "I have verified the conjecture in all (4096 choose 3) = 11,444,858,880 cases in which 1 ≤ s1 < s2 < s3 ≤ 4096." Case I (s3 = s1+s2) has an explicit closed-form period.
- **Moriwaki, "Subtraction Nim with Continuous Parameters", arXiv:2606.11658v1 (2026-06-10)** — restates the conjecture as Conjecture 1 ("… is periodic with a period a + b, b + c or c + a", with c ≠ a+b per Remark 7) and credits Ward 2016. **Decisive definition**: Definition 2 — "We call p (resp. x0) a period (resp. preperiod) of f … **The minimality is not required for them**, and if p is minimal among the periods of f, then we call p the minimum period of f."
- **Miklós–Post, arXiv:2312.02426v1 (2023-12-05)** — about 0/1 winning-position periods with seeds; its own Conjecture 1 is `Per({a,b,c}) < 2c` (no seed, verified c ≤ 200). It does not restate Ward's nim-value conjecture in that form; it is a related but distinct statement (Ward ⟹ it, since the w-period divides the nim period m and m | s_i+s_j ≤ b+c < 2c).

**Quantifier reading (faithful correspondence).** Under the sources' own Definition 2, "is periodic with a period a+b, b+c or c+a" means: for some p ∈ {a+b, b+c, c+a}, g(n+p)=g(n) for all n ≥ n0. Since the set of eventual periods of a sequence is exactly the multiples of its minimal eventual period m, the literal conjecture is equivalent to

**m | (a+b) or m | (b+c) or m | (c+a)**,  where m = minimal eventual period of the nim sequence.

## 3. r302's proposed refutation is INVALID

r302 (shortlist rank 1; `screening/witness-375237.json`) claimed S=(1,3,5) has eventual period 2 ∉ {4,8,6}, "already contradicted". That uses the **minimal**-period reading. Under the source's Definition 2 (minimality not required), 4 = a+b **is** a period because the minimal period 2 divides 4. Exact recheck (state-cycle criterion, `scripts/nim_exact.py single 1 3 5`): preperiod 0, m=2, cycle (0,1); 2 | 4, 2 | 8, 2 | 6. The witness fails; the same holds for all 37 r302 witnesses (each has m=2 and even sums; see `verification/r302_witnesses_recheck.json`). No reading of "period" in the source supports a counterexample claim: the minimal reading is expressly excluded by Definition 2, and Ward's original Case II is explicitly the divisibility form.

## 4. Decisive exact evidence (divisibility form)

Method (no finite-tail guessing): the window of the last c nim-values is a deterministic state; a first repeated state proves the infinite sequence equals the detected cycle repeated; the minimal period m is computed from the cycle. Trajectory initialized by the literal mex rule g(n)=mex{g(n−s): s∈S, s≤n}, g(0)=0 (verified independently).

- **Full exact scan, all 9500 triples 0<a<b<c≤40 with c≠a+b**: 0 violations of the divisibility form; 0 inconclusive; max preperiod 572; max m 79; 380 sampled independent crosschecks (fresh recompute + far-tail period/minimality checks) all OK (`verification/scan-B40.json`, `scripts/scan3.py`).
- Earlier scans: c≤25 (2156 triples, `verification/scan-B25.json`), c≤20 with Ward's gcd characterization p = gcd{s_i+s_j : m | s_i+s_j} verified on all 1050 triples (`verification/scan2-B20.json`).
- Consistent with Ward's own computational verification to s3 ≤ 4096 (2016) — no counterexample exists below that bound; our contribution is exact per-triple certificates (state cycle), not the bound.

## 5. Mechanism investigation (why the conjecture resists proof)

1. **Window-of-agreement induction**: g(n+p)=g(n) for c consecutive n self-propagates (mex of identical value-sets). So periodicity reduces to producing c consecutive agreements — no general construction known; this is exactly the gap in Moriwaki's region-by-region approach.
2. **Periodic-solution classification — REFUTED as a route.** The eventual behavior of the game is a solution G: ℤ_L → {0..3} of G(x)=mex{G(x−a),G(x−b),G(x−c)} with minimal period L. We enumerated **all** solutions for small triples (`scripts/solutions_enum.py`, `verification/sweep-solutions-B9.json`). Bad solutions exist **inside the conjecture's scope (Case II)**: e.g. S=(1,3,6) (sums 4,9,7) has 24 solutions on ℤ₁₂ with minimal period 12 (12 ∤ 4,9,7); independently verified tuple (0,2,1,2,0,2,1,3,0,3,1,3); likewise S=(3,5,6) and S=(6,7,9) (L=12), and S=(3,4,7) (Case I, L=8, 96 solutions). The true game never reaches these cycles. **Therefore any proof must use reachability from the true initial condition (the greedy/P-position structure), not the functional equation alone.** This is, to our knowledge, not stated in Ward/Moriwaki/Miklós–Post, but it is an observation about mechanism, not a certified theorem, and is not claimed for credit.
3. **Win/lose reduction**: the minimal period of w(n)=[g(n)≠0] generally differs from m (e.g. (1,2,4): m=3, m_w=4; 550+ mismatches at c≤20), so no equality route through P-positions.

## 6. Prior bridge / status

- r304 (`accepted-exclusions.json`, `historical-dispositions.json`, hashed in `sources/provenance.json`): **no** entry touches 375237, Subtraction Nim, Ward, Moriwaki, 2312.02426, or 2606.11658 (exhaustive key/value walk). Not in retired 371202/338289, parked 368302, assigned 322922, or the r320 batch.
- Public status: open problem (Nowakowski's unsolved-problems list lineage; Ward 2016 conjecture with computation only; Moriwaki 2026 proves it for infinitely many regions and states Conjecture 1 as open). No public resolution found; arXiv listings of both papers carry no newer versions (v1 each, fetched 2026-10-30/31 UTC).
- The proposed hypothesis (bounded_counterexample) is **retired as worded**; the underlying conjecture **survives** and is parked as an open problem.

## 7. Gaps

- No proof of the divisibility form in full scope; the periodic-solution route is provably insufficient (§5.2), so a proof must control reachability of cycles from the mex trajectory — no tractable full-scope mechanism found within caps.
- Enumeration of solutions was complete only for L ≤ 12 on triples with a<b<c≤9 (plus targeted triples); larger L unexamined (node caps).
- No Lean formalization (parked lane; not applicable to a park disposition).

## 8. Failures (candid)

- First trajectory computation left g[1..c−1] uninitialized (detected by crosscheck mismatch); fixed.
- Preperiod/divisibility direction bugs (m%p vs p%m; valid-region truncation); fixed after crosscheck flagged them.
- First DFS enumerator used an invalid list comprehension and a wrong constraint-scheduling key (constraint checked before its own cell assigned); fixed and revalidated against the known game cycle.
- First enumerator run was killed by the 512MiB/230s guard (too slow); rewritten with O(1) per-node constraint checks, immediate coloring prune, and streaming output.
- No 403/429/access issues; no retries needed.

## 9. Provenance

All fetched bytes with UTC and SHA256: `sources/provenance.json`. Helper runs executed via `sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py` with `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B`; all runs within 512MiB / CPU 210s / wall 230s. Runnable checker: `scripts/check_all.py` (reruns the decisive computations and prints PASS/FAIL).
