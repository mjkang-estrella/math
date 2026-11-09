# High-dimensional Level-2 covering sieve (k >= 3 free far digits)

Research sub-agent report, 2026-10-20/21 (author of `verification/highdim/{gen_hd,checkhd,run_target}.py`;
sections 1-3 incorporate wording from the parallel session math-02, which drafted them from this
code). Labels: **PROVED** = mathematical implication, or a complete certificate cover that was checked
by an independent checker; **COMPUTED** = an executed finite calculation; **CONJECTURAL** = unproved
expectation. Nothing here proves the general persistence conjecture.

**Ownership (agreed with math-02).** This note and `verification/highdim/` top level + `hd2/` belong to
this agent; scope = target 112 and target 111132. Target 14112 and the small targets 16/24/32 are handled
by Codex continuations (`verification/highdim/codex/`, `notes/highdim_codex*.md`) and the symmetric-
certificate agent (`verification/highdim/sym*/`, `notes/highdim_sym.md`); their counts are theirs, not
claimed here.

## 0. Bottom line

| target | open before (C = E enumeration) | closed here | still open | status of closed part |
|---|---:|---:|---:|---|
| 112 | 12 (all >= 3 far digits) | **12** | 0 | PROVED (120 certs; checkhd 120/120, unchanged checknd 106/106 ordered) |
| 111132 | 332 | **122** (all with <= 4 free far digits in every slice) | 210 (124 k=5, 66 k=6, 18 k=7, 2 k=8) | PROVED (5876 certs; checkhd 5876/5876, unchanged checknd 5648/5648 ordered) |
| 14112 | 870 + S387 | not in scope here | -- | see notes/highdim_codex*.md, notes/highdim_sym.md |

**PROVED (with the trust base of section 5): target 112 is closed for all lengths.** Its Level-2
members are exactly 1728 and 2187 (both in configurations closed earlier by C/A; the 12 formerly open
configurations contain no solution at any length). For 111132 the 122 closed configurations contain no
solution at any length; 210 configurations (5..8 free far digits) remain open, so 111132 is *not* closed.

## 1. Equation and domain

**PROVED.** If a decimal integer n of length L has low-position excess
S = sum_{p<3}(d_p-1)10^p and remaining non-1 digits d_i at distinct positions q_i >= 3, then

    X = 9n = 10^L + sum_i c_i 10^{q_i} + K,   c_i = 9(d_i-1),  K = 9S-1.

For these targets 5 does not divide the digit product, so a 7-smooth n is 2^x 3^y 7^z. On a slice with
K > 0, t0 = v2(K) and all coordinates (L and every free q_i) >= qmin > t0, v2(X) = t0, and the equation
to certify is X = 2^{t0} 3^a 7^w (a includes the factor 9; allowing all a only enlarges the domain).

**PROVED (slice cover).** `run_target.slices` covers every placement: while some free digit has floor
<= v2(K), branch on fixing it at each position in [floor, v2(K)] (adding c_i 10^q to K) or raising its
floor to v2(K)+1; repeat with the new valuation. Emitted domains may be larger than the true pieces
(relaxed floors, coinciding fixed positions), which is harmless for exclusion; recorded solutions would
have to be checked against the digit configuration (none occur). The only real points outside every
certificate domain are those with L < qmin of a 0-free-digit slice; max qmin is 13 (t=112) and 27
(t=111132), and they are covered by the digit-level brute force over all 7-smooth n < 10^100
(`coverage.py`; also E/E2's L <= 600 enumerations). **COMPUTED:** my `slices` agrees with GLM's
`pipeline.slices` as a set on all 12 configurations of t=112.

## 2. Certificate semantics and soundness (no new kill types)

**PROVED.** A node is a residue vector r modulo a common modulus M for all coordinates (L, q_1..q_k).
With j = v3(M): ord_{3^{j+2}}(10) = 3^j, so X mod 3^{j+2} is constant on the node; it fixes a exactly or
gives a >= j+2. If 6 | M, with i = v7(M): ord_{7^{i+1}}(10) = 6*7^i, so w is fixed or w >= i+1;
otherwise w >= 0. For a prime p > 7 with ord_p(10) | M, T = X 2^{-t0} mod p is constant on the node;
after dividing by 3^{a0}7^{w0} it must lie in {1}, <3>, <7> or <3,7> (according to which exponents are
unbounded); failure (or T = 0) is a `prime` kill. If ord_p(10) does not divide M the checker re-tests
every lift to lcm(M, ord_p(10)). Internal nodes list children; every other lift must be killed by a
listed `rest` prime. The root is the whole space mod 1. At an `sz` leaf a and w are both exact, X = N is
one integer, and the checker enumerates every domain point with X = N exactly. The only kills used are
the existing `prime` kills plus `sz` leaves -- exactly the format of `verification/indep/checknd.py`.
No pin/pin2 kills.

**PROVED (orderings, cf. REPORT_E).** Prime kills act on full residue classes and never use the order of
the q_i, so a tree covers every ordering at once; ordering only matters at `sz` leaves and in the brute
box. Accordingly:
* k <= 2 free far digits: one certificate per **distinct ordering** of the coefficient multiset, domain
  `ordered` (L > q_k > ... > q_1 >= qmin), checked by the **unchanged** `indep/checknd.py` and by `checkhd.py`;
* k >= 3: one certificate with meta `"domain": "unordered"` (q_i pairwise distinct, qmin <= q_i < L, no
  order between them), i.e. the union of all orderings; `checkhd.py` enumerates `sz` points and the brute
  box over all permutations. Tamper test `ctrl1 relabelled ordered` (section 5) shows a solution with the
  coefficients in non-ascending position order is caught in unordered mode and missed in ordered mode.
A configuration is counted CLOSED only if every slice and every distinct ordering is certified.

## 3. Why the old sieve stalled, and what changed (the method)

**COMPUTED diagnosis.** The L2c sieve refined greedily along the 3-adic ladder. The real obstruction is
the **double ladder**: classes with X == 0 mod 3^{j+2} AND mod 7^{i+1} (a and w both unbounded) form a
codimension-2 family that dominates the survivors (e.g. dim 5, K=89: 29,795 of 29,813 survivors at
M = 72). For such a class the test is T notin <3,7> mod p, and

**PROVED (key observation).** for unbounded a and w, membership of T 3^{-a0} 7^{-w0} in <3,7> does not
depend on a0, w0: the double-ladder test depends only on x mod ord_p(10), not on the 3-/7-adic depth.
Hence refining deeper in 3 buys nothing for the double ladder; what kills it is *many primes whose
ord_p(10) divides a smooth, highly composite M*. This is idea (a) of the brief, refined: no single small
<3,7> (p=37 type) suffices for k >= 3, but the joint action of all primes with ord_p(10) | 15120 does.

**Method (COMPUTED that it works; CONJECTURAL that it always will).**
* Prime supply (`supply.py`): all p > 7 with ord_p(10) | N found by factoring Phi_d(10) (phi(d) <= 72)
  and by scanning p = 1 + d t <= B. supply_B: N = 2^6 3^8 5^2 7^4 11 13, B = 4e8 (1589 primes);
  supply_C: N = 2^6 3^10 5^2 7^6 11 13 (1756); supply_D: N = 2^6 3^13 5^2 7^7 11 13, B = 1.5e9 (2134).
  The supply is a search aid only; checkers re-derive primality and orders.
* Phase A (`gen_hd.py`): breadth-first refinement along a fixed schedule, for dim 5
  (2,3,7,3,2,2,2,3,5) -> M = 15120 = 2^4 3^3 5 7; for dim 4 (2,3,2,5,3,2,7) -> 2520. Lifts are killed by
  the strongest aligned prime for their signature type. Measured, dim 5, K=89, [9,9,9,54]:
  32, 477, 26234, 133317, 14830, 39040, 76910, 8346, **18** survivors at M = 2..15120; all 18 are
  single-ladder.
* Phase B: per-node deepening: a factor that kills the class outright if one exists, else 3 if only a
  is unbounded, 7 if only w is unbounded, else the better of 3/7. Exact (a,w) -> `sz` leaf.
* The persistent survivors are **spurious solutions**: integer or rational points of the relaxed
  equation outside the domain (negative or coinciding positions). Examples: (L,q) = (2;0,0,3,0) for
  K=89 gives X = 9261 = 3^3 7^3; L = -1 gives 729 = 3^6; for t=111132 S616, (4;3,3,3,1) gives
  151263 = 3^2 7^5; S615 (2;4,3,1,5) gives 2*3^12*7. A sieve can never separate such a point by
  congruences, but once a and w are pinned it becomes an `sz` leaf with an empty in-domain list.
  **PROVED/COMPUTED:** to pin w = w* one needs 7-adic depth w*+1, and to kill the neighbouring 7-ladder
  classes (which share every residue with the spurious point modulo the old M) one needs primes with
  7^{w*} | ord_p(10); likewise 3^{a*-1} for a. This is exactly why supply_C (7^5, 7^6) and supply_D
  (3^11..3^13) were needed: run B closed 34 configs, C closed 83 more, D the last 5.

## 4. Checkers

* `checkhd.py` (any dimension) re-implements `checknd.py` semantics from its spec with the `unordered`
  domain option; imports only `vp, order, lcm, isprime` from Agent A's `indep/nt.py`; shares no code with
  the generator (its `sz` enumeration is a bounded search, the generator's is a digit decoder). It adds:
  root must be the whole space; stored residues/moduli/parent links must agree with the tree; per-node
  checks run in parallel after a serial structural pass; signature tables are period-asserted.
* **COMPUTED cross-validation:** on all 503 pre-existing certificates (GLM L2c 464 + Agent A),
  `checknd` and `checkhd` agree on all 500 full-root certificates (all PASS); the 3 disagreements are
  Agent A's positive controls rooted at a single class, which `checkhd` rejects by design.
* **COMPUTED tamper/controls (`tamper.py`, 20/20 met):** a dim-4 control whose only solution has
  coefficients in non-ascending order (PASS unordered; FAIL when relabelled ordered; FAIL when the
  solution is deleted or its leaf replaced by a prime kill; the ordered certificate for the reversed
  coefficient order records it); a dim-3 control passing both checkers; and, on a control and a real
  t=112 certificate: dropped child subtree, bogus rest prime, perturbed child residue, corrupted leaf,
  partial root, changed K -- all FAIL for the intended reason.
* math-02 reports re-checking the t=112 certificates with its own dimension-general patch of checknd
  (`verification/v14_checknd_hd.py`); its verdicts are recorded in the parent log, not here.

## 5. Trust base of the PROVED claims

(i) the master equation and parity/config enumeration (C, E, E2 agree on the open lists);
(ii) the slice cover of section 1 (own code; equal to GLM's on t=112);
(iii) checker correctness: unchanged `checknd.py` for the ordered certificates, `checkhd.py` for all;
(iv) the brute force < 10^100 for points below certificate floors. No Baker-type input is used.

## 6. Results

### Target 112 (12/12 closed) -- PROVED

| S_low | far | slices | certs | nodes |
|---:|---|---:|---:|---:|
| 1 | 9,9,9,54 | 38 | 40 | 473,980 |
| 1 | 9,27,54 | 40 | 43 | 32,049 |
| 10 | 9,9,9,54 | 1 | 1 | 299,232 |
| 10 | 9,27,54 | 1 | 1 | 35,103 |
| 11 | 9,9,54 | 1 | 1 | 35,156 |
| 16 | 9,9,9 | 1 | 1 | 29,244 |
| 30 | 9,9,54 | 1 | 1 | 38,576 |
| 61 | 9,9,9 | 1 | 1 | 23,511 |
| 101 | 9,9,54 | 1 | 1 | 18,362 |
| 110 | 9,9,54 | 1 | 1 | 21,871 |
| 601 | 9,9,9 | 28 | 28 | 43,664 |
| 610 | 9,9,9 | 1 | 1 | 20,553 |

120 certificates (`verification/highdim/certs/t112/`, 117 MB, 1.07M nodes): checkhd 120/120 PASS,
unchanged checknd 106/106 PASS on the ordered ones (`logs/check112_*.log`). No certificate records an
in-domain solution. `coverage.py 112`: members < 10^100 are 1728, 2187, both in other (already closed)
configurations; max floor 13.

### Target 111132 (122/332 closed)

Closed: every configuration whose slices have <= 4 free far digits -- 18 configurations with 3 far digits
and 104 with 4 -- 5,609 slices, 5,876 certificates (5,648 ordered, 228 unordered), 50.2M nodes, in
`verification/highdim/hd2/certs/t111132/` (5.3 GB); per-configuration data in
`hd2/results_t111132.json` (includes S636 {54,72,72}, which needed supply_C). No certificate records an
in-domain solution; `coverage.py 111132`: no members < 10^100, max floor 27.
**PROVED (checked):** `verify_results.py` re-derives each closed configuration's required file list
(all slices, every distinct ordering), finds 0 missing, and gets checkhd PASS 5876/5876 and the
unchanged checknd PASS 5648/5648 (all ordered certs). Result: 122/122 configurations fully verified
(`hd2/logs/verify_111132.{log,json}`, with per-file sha256 prefixes).

Still open (not attempted to completion): 124 configurations with a 5-free-digit slice, 66 with 6, 18 with
7, 2 with 8.

## 7. What resists, and why

* **Dimension >= 6 (5+ free far digits).** **COMPUTED:** the flat Phase-A BFS for K=5498,
  [18,18,54,54,72] exceeded 4 GB at the 7-refinement level (7^6 = 117,649 lifts per node). The
  certificate format forces a common modulus and enumeration of every lift, so cost grows like f^dim.
  The symmetric (orbit) certificates of `notes/highdim_sym.md` reduce this by n!-type factors for equal
  coefficients and are the natural route; I have not evaluated them.
* **Spurious solutions with large exponents.** **PROVED (mechanism) / COMPUTED (instances):** a relaxed
  solution with exponent a* (or w*) needs primes with 3^{a*-1} (7^{w*}) dividing ord_p(10); such primes
  are large (p > 3^{a*}), so a spurious point with, say, a* >= 15 would need p beyond the scanned
  1.5e9. A tamper control with a = 17 indeed could not be closed. No real configuration of t=112/111132
  hit this limit.
* **No termination theorem.** **CONJECTURAL:** every configuration admits a finite cover (Skolem-type
  local-global expectation; heuristic: kill power ~ tau(M) vs class growth ~ dim*log M). A profinite
  point (all x mod M surviving for every M) would block the method entirely; none was observed.
* Idea (c) (induction on the top digit) and (d) (Baker) were not needed and not used.

## 8. Reproduction

```
cd verification/highdim
python3 -I supply.py "2**6*3**8*5**2*7**4*11*13" 4e8 supply_B.json   # also _C, _D (see section 3)
python3 -I run_target.py 112                                          # -> results_t112.json, certs/t112
HD_OUT=$PWD/hd2 HD_SUPPLY=supply_C.json python3 -I run_target.py 111132 - 4
HD_OUT=$PWD/hd2 HD_SUPPLY=supply_D.json python3 -I run_target.py 111132 615,832,836,238,638 4
python3 -I verify_results.py hd2/results_t111132.json hd2/certs/t111132 hd2/logs/verify_111132.json
python3 -I checkhd.py <cert> [brute_L] [workers];  python3 -I ../indep/checknd.py <ordered cert>
python3 -I tamper.py;  python3 -I coverage.py 112;  python3 -I coverage.py 111132 hd2/results_t111132.json
```
(all run under `ulimit -v 4000000`, stdlib only).
