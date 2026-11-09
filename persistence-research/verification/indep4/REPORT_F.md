# REPORT_F — independent audit of the nd-sym closures (target 14112, 121 configurations of dimension 6–7)

Auditor: review sub-agent F. Everything is in `verification/indep4/`; stdlib Python, run as `bash -c 'ulimit -v 8000000; python3 -I …'`. Nothing outside `indep4/` was modified (the one side effect is that importing `check_sym.py` for the differential test was done with `sys.dont_write_bytecode=True`; `indep2/` and `highdim/` untouched). Nothing was committed.

## Verdict

**All 121 closures are independently confirmed.** My own checker `check_sym_F.py` (written from `notes/highdim_sym.md` and first principles before `check_sym.py`/`gen_sym.py` were opened) accepts all 121 certificates, and my own coverage map (own enumeration of the 1640 configurations of target 14112, checked equal to E's) puts each of the 121 configurations inside exactly one accepted certificate with the right K, groups and domain. M's `check_sym.py` and mine never disagree on any test I could construct (see §4).

| kill type | verdict |
|---|---|
| (a) multiset classes / lifts | **sound** |
| aligned prime kill (`ord_p(10)` divides `M`) incl. 3/7 signatures | **sound** |
| (b) sumset kill (`ord_p(10) ∤ M`) | **sound** (conditions: sumset over all `q mod d` compatible with the class mod `gcd(d,M)`, *every* element must miss the necessary set) |
| mod-8 pin (`pin2`) | **sound with condition** `qmin ≥ v2(K)+3` (enforced by both checkers) |
| (c) decimal-tail coset (`pin_digits = k`) | **sound with condition** `k ≤ min(3, qmin)`; the 2-adic part of the modulus is `2^{max(k−t0,0)}` (divide by `2^{t0}` once) |
| (d) size leaves and brute box | **sound**. (All 84 size leaves of these certificates have `N ≤ 250047 < 10^8 ≤ min X`, hence are empty for trivial size reasons; the brute box is a consistency check, not part of the proof) |

No unsound kill type was found, and no certificate was rejected.

**Scope extension (Part B, at the end):** on the 398 further sym2 closures I audited the tail/mod-8 kills specially (sound with conditions that hold in all 54 764 sym2 metadata records), replayed a stratified random sample of 487 sym2 certificates (487/487 PASS) and independently covered a sample of 63 configurations with 13 087 certificates (63/63 covered, all PASS). The other ≈ 335 sym2 closures were *not* individually replayed.

## 1. Mathematical claims relied on by each kill type, with proofs

(Written **before** `check_sym.py` / `gen_sym.py` were opened; from `notes/highdim_sym.md` + first principles. My checker is `check_sym_F.py`.)

### 0. Setting and notation

A certificate has groups `(c_g, m_g)`, `g = 1..G` (distinct `c_g > 0`), `F = Σ m_g` slots, integers `K > 0`, `qmin`, `t0 = v2(K)`, `qmin > t0`.
The **domain** is 𝒟 = all `(L, (q_{g,j}))` with pairwise distinct `q_{g,j}`, `qmin ≤ q_{g,j} < L`.
`X(pt) = 10^L + Σ_g c_g Σ_j 10^{q_{g,j}} + K`.
To show: `X(pt) ≠ 2^{t0} 3^a 7^w` for all `pt ∈ 𝒟`, except the listed points.

A *class* mod M is `κ = (L mod M ; sorted residues mod M of group 1; … ; group G)`. `S(κ) = {pt ∈ 𝒟-or-the-larger-labelled-space : class_M(pt) = κ}`.
For **all** kills below I work on the larger space 𝒟' (positions arbitrary integers ≥ qmin, *not necessarily distinct*, `L` arbitrary ≥ qmin). `𝒟 ⊆ 𝒟'`, and every argument is a congruence argument, so a kill valid on `S(κ) ∩ 𝒟'` is valid on `S(κ) ∩ 𝒟`.

**(V2)** If `pt ∈ 𝒟'`, then `v2(X) = t0`. Proof: every `10^q` with `q ≥ qmin ≥ t0+1` and `10^L` (`L ≥ qmin` since `L > q`; on 𝒟' with no slot, it's `L ≥ qmin` by definition) is divisible by `2^{t0+1}`, while `2^{t0} ‖ K`. ∎
Hence "X smooth" ⇔ `X = 2^{t0} 3^a 7^w`, `a, w ≥ 0`, and `Y := X/2^{t0}` is an odd integer.

### 1. (SIG) Signature of a class
Let `j = v3(M)`. `10 = 1 + 9`, so `ord_{3^{j+2}}(10) = 3^j` (lifting-the-exponent: `v3(10^n − 1) = 2 + v3(n)`). Since `3^j | M`, for `q ≡ r (mod M)`, `10^q ≡ 10^r (mod 3^{j+2})`. So `X mod 3^{j+2}` is a function of the class: `x3`.
If `x3 ≠ 0` then `v3(X) = v3(x3) < j+2`: the exponent `a` is **exact**. If `x3 = 0` then `a ≥ j+2` (a lower bound only).
Similarly, if `6 | M`, `i = v7(M)`: `ord_{7^{i+1}}(10) = 6·7^i` (`10^6 = 1000000 ≡ 8 (mod 49)`, so `v7(10^6 − 1) = 1`, lifting the exponent), which divides `M`. `w` is exact or `≥ i+1`. If `6 ∤ M`: no information on `w` (`w ≥ 0`).

### 2. (a) Multiset classes: children of a node partition the parent's set
Let `κ` be a class mod `M` and `M' = fM`. Define `ρ` = "reduce every residue mod `M` and re-sort". For every point, `ρ(class_{M'}(pt)) = class_M(pt)` (sorting commutes: the multiset of reductions is the reduction of the multiset). Therefore
`S(κ) = ⊔_{κ' : ρ(κ') = κ} S(κ')`
(disjoint because `class_{M'}` is a function; covering because `class_{M'}(pt)` is such a κ').
**Enumeration of `Lift(κ) = {κ' : ρ(κ') = κ}`.** `L' ∈ {L + iM : 0 ≤ i < f}`. For a group with sorted residues `κ_g`, let residue `b ∈ [0,M)` occur `h_b` times. A multiset `κ'_g` with `ρ(κ'_g) = κ_g` splits uniquely by the residue-mod-`M` of its elements into sub-multisets `κ'_{g,b}` of size `h_b` over `{b, b+M, …, b+(f−1)M}` (the `b < M` are distinct so the pieces cannot mix). A multiset of size `h` over `f` symbols ⇔ its multiplicity vector `(n_0..n_{f−1})`, `Σ n_i = h`, i.e. a weak composition of `h` into `f` parts. Therefore
`|Lift(κ)| = f · Π_g Π_b C(f + h_b − 1, h_b)` and `Lift(κ)` = the product of independent choices (L; and for each group and each distinct `b`, one weak composition). That is what `check_sym_F.group_lifts` enumerates, and `test_F.py::T1` checks it against exhaustive labelled enumeration (`Σ_{κ'} #labelled tuples with class κ' = f^{F+1} · #labelled tuples with class κ`).
**Why reducing the sorted tuple coordinatewise is wrong:** `(b1 + i1 M, b2 + i2 M)` sorted by value is not sorted by `b`; the multiset must be re-sorted after the lift, and a lift with `i`'s assigned to *positions in the sorted tuple* produces the same child many times / misses some.
**Why one representative per equal-coefficient group is enough:** `X` is symmetric in the slots of a group, so the *set* of values of `X` over `S(κ)` is invariant under the permutation of slots; the class records exactly the multiset, so nothing is lost. Actual solutions are sets of positions per group, hence have a well-defined class at every modulus.
**Global argument (induction down the tree):** a point `pt` with class `κ` at a node lies in exactly one lift; if that lift is not an explicit child it must be killed (below), otherwise `pt` continues to the child. Moduli strictly increase and the tree is finite, so every point ends at a leaf or in a killed lift.

### 3. (AL) Aligned prime kill (`ord_p(10) | M`)
`p > 7` prime, `d = ord_p(10) | M`. For `q ≡ r (mod M)`, `10^q ≡ 10^r (mod p)`, so `T := X mod p` is a function of the class.
If `X = 2^{t0} 3^a 7^w` then `T ≠ 0` (`p ∤ 2·3·7`) and `Y = T·2^{−t0} = 3^a 7^w (mod p)`.
- exact `a = a0`: factor `3^{a0}`; free `a ≥ a_lo`: `{3^a : a ≥ a_lo} = ⟨3⟩` as a subset of `F_p^*` (finite cyclic group, infinite arithmetic progression of exponents covers the whole subgroup). Same for `7`.
- So `Y ∈ 3^{e_a}7^{e_w}·H`, `H = ⟨3 if a free, 7 if w free⟩`, `|H| = lcm(ord 3, ord 7)` (the subgroup of a cyclic group generated by two elements has the lcm order). Membership: `y ∈ gH ⇔ (y/g)^{|H|} = 1 ⇔ y^{|H|} = g^{|H|}`.
Kill iff `T = 0` or `Y ∉ gH`. ∎

### 4. (b) The sumset kill (`ord_p(10) ∤ M`)
Let `d = ord_p(10)`, `g = gcd(d, M)`. If `q ≡ b (mod M)` then `q ≡ b (mod g)` (as `g | M`), hence `q mod d ∈ E_b := {e ∈ [0,d) : e ≡ b (mod g)}` and `10^q ≡ 10^e` for one such `e`. Put `S_b = {10^e mod p : e ∈ E_b}` (depends only on `b mod g`).
**Claim.** For every `pt ∈ S(κ) ∩ 𝒟'`: `X mod p ∈ 𝒮(κ) := K + S_{L} + Σ_g c_g (S_{b_{g,1}} + … + S_{b_{g,m_g}})` (Minkowski sums; one summand per *slot*, the `b`'s being the residues listed in `κ`).
Proof: slot `(g,j)` has residue `b_{g,j}` (some assignment of the multiset to the slots; the sum is symmetric, so which one is irrelevant), and `10^{q_{g,j}} ∈ S_{b_{g,j}}`. Add. ∎
`𝒮(κ)` is computed over **exactly the residue multisets consistent with the class**: each slot ranges independently over all `q mod d` compatible with its residue mod `M`. This is a superset of the values attained by `𝒟` (it ignores distinctness and collisions) and uses only information in `κ` (not the stronger signatures of un-enumerated children).
**Kill rule.** Let `Allowed ⊂ F_p^*` be the necessary set for `Y` from §3 (possibly refined by the pins of §5, §6). If `(2^{−t0}·𝒮(κ)) ∩ Allowed = ∅`, then no `pt ∈ S(κ)` has smooth `X`: for such a `pt`, `Y ≡ 2^{−t0}X ∈ 2^{−t0}𝒮(κ)` and `Y ∈ Allowed` would contradict the emptiness. The kill requires **every** element of the sumset to miss (not just one representative). ∎
A "single representative" (taking `q mod d = r`) would be unsound; `tamper_F.py` constructs a leaf where this wrong rule would kill but the true sumset does not, and the checker rejects it.

### 5. (P2) The mod-8 pin
Assume `qmin ≥ t0 + 3`. Then `2^{t0+3} | 10^q` for `q ≥ qmin` and for `10^L` (`L ≥ qmin`), so `X ≡ K (mod 2^{t0+3})`, thus `Y = X/2^{t0} ≡ K/2^{t0} (mod 8)`. `3^a 7^w mod 8 = 3^{a mod 2} 7^{w mod 2}` takes the four distinct odd residues `1, 3, 7, 5` for `(a,w) mod 2 = (0,0),(1,0),(0,1),(1,1)` (bijection). So `(a mod 2, w mod 2)` is forced by `K`. If `a` is exact with the wrong parity: impossible. If `a` is free: `a` ranges over one parity class, i.e. `3^a ∈ 3^{α}⟨9⟩`. This is a special case of §6 with modulus `E = 8`.

### 6. (c) The decimal-tail coset pin
Let `k ≤ min(3, qmin)`; every position and `L` are `≥ qmin ≥ k`, so `10^k | 10^q` for all terms: `X ≡ K (mod 10^k)`. Write `X = 2^{t0}Y`, `K = 2^{t0}K0`. Then `2^{t0}(Y − K0) ≡ 0 (mod 2^k 5^k)`:
- the `5^k` part: `gcd(2^{t0},5) = 1`, so `Y ≡ K0 (mod 5^k)`;
- the `2^k` part: `2^{t0} (Y − K0)` ≡ 0 mod `2^k` ⇒ `Y ≡ K0 (mod 2^{max(k − t0, 0)})` (**divide by `2^{t0}` once**; if `t0 ≥ k` the condition is empty).
So `3^a 7^w ≡ K0 (mod D)`, `D = 5^k 2^{max(k−t0,0)}`. Combining with §5 (same right-hand side `K0`): modulus `E = 2^{max(3·[pin2], k − t0, 0)} 5^k`.
Let `A = ord_E(3)`, `W = ord_E(7)`. The set of admissible residue pairs is `P = {(α,β) ∈ Z/A × Z/W : 3^α 7^β ≡ K0 (mod E)}`. Exact signatures keep only pairs with `α ≡ a0 (mod A)` / `β ≡ w0 (mod W)`.
At a prime `p`: for a free `a`, `{3^a : a ≥ a_lo, a ≡ α (A)} = 3^α⟨3^A⟩` (a finite-group argument again; the lower bound `a_lo` removes nothing). So `Allowed = ⋃_{(α,β)∈P'} 3^{e_a}7^{e_w}·⟨3^A if a free, 7^W if w free⟩`, and the kill rule of §3/§4 is applied to this union of cosets.
**The pin holds on the WHOLE domain**, not only on a sub-region, because the only property used is `q ≥ k` for every position and for `L`; this is guaranteed by `k ≤ qmin`. The classical errors are (i) pinning with `k > qmin` (a position `q < k` contributes a term not divisible by `10^k`); the checker enforces `k ≤ min(3,qmin)` and the tamper tests exercise it; (ii) dividing the congruence by `2^{t0}` twice (the exponent of 2 in the modulus is `k − t0`, not `k − 2t0`); (iii) forgetting that the mod-`2^k` part is vacuous once `t0 ≥ k`.

### 7. (d) Size leaves and the brute box
A size leaf needs exact `a0, w0` from §1. Then `X = N := 2^{t0}3^{a0}7^{w0}` is one fixed integer; because all terms are positive, `10^L ≤ N − K − …`, so only finitely many `L` are possible, and for each `L` the identity `Σ c 10^q = N − K − 10^L` is solved by exhaustive depth-first search over *strictly decreasing* positions (every injective placement is enumerated exactly once: a placement is the same as the decreasing list of its `(position, coefficient)` pairs). The solutions are filtered by the leaf's class and must equal the declared list. No assumption of "no carries" is made.
Brute box: every point with `L ≤ B` is enumerated; every smooth `X` must be located (by descending the tree with its own residues) in a size leaf that lists it, and the set of leaf-declared solutions with `L ≤ B` must equal the brute set.

### 8. Soundness theorem for a passing certificate
If the checker accepts: (1) the root class is the all-zero class mod 1 = the whole domain; (2) by §2 each point goes to exactly one lift of its class; (3) a non-explicit lift is killed, and by §3–§6 contains no smooth point; (4) explicit children recurse; (5) leaves: killed by a prime (no smooth point) or a size leaf (all smooth points of the class listed, §7). Hence the set of smooth points of 𝒟 equals the union of the declared solution lists. ∎

## 2. My checker and its run on the 121 certificates (task 2)

`check_sym_F.py` — stdlib only, no import of generator/projection/legacy code. It checks: meta (format, `unordered`, `scope=full`, distinct positive coefficients, `qmin > v2(K)`, `pin2 ⇒ qmin ≥ t0+3`, `pin_digits ≤ min(3,qmin)`, root = all-zero mod 1); canonical sorted residues; node/parent/modulus headers; unique ids; no cycles; reachability; child ⊂ `Lift(parent)` (weak compositions, own code); every non-explicit lift killed by a listed prime, re-derived from scratch (primality by trial division, orders by factoring `p−1`, signatures, sumset, pin cosets); size leaves by an own DFS over strictly decreasing positions; a brute box (`L ≤ 11`, every injective placement) that must agree with the leaf-declared solutions. Every kill is also classified by the *weakest* pin variant that still kills it (`plain` < `p2` < `tail` < `both`) so that the contribution of the new kill types can be counted.

Run: `run_all.sh files121.txt logs/all 11` (16 parallel processes, ≈ 25 min wall on a loaded machine). Per-certificate JSON: `logs/all/*.json`; aggregate: `summary_F.json`.

| item | count |
|---|---|
| certificates checked | 121 (dim 6: 89, dim 7: 32) |
| **PASS** | **121** |
| FAIL | 0 |
| tree nodes (explicit) | 62 676 |
| refinements (lifts) enumerated and each either child or killed | 112 873 032 |
| killed lifts (all re-verified) | 112 810 477 |
| leaves | 198 = 114 prime leaves + 84 size leaves |
| declared / found solutions (all size leaves) | 0 / 0 |
| brute-box points (`L ≤ 11`) / smooth hits | 360 600 / 0 |

Pass/fail per kill type (instances of verified kills; "unique" = distinct (prime, signature, reduced class) cache entries actually evaluated):

| kill type (weakest sufficient variant) | instances verified | unique | PASS | FAIL |
|---|---|---|---|---|
| aligned prime, plain (no pin needed) | 105 617 519 | 51 011 716 | all | 0 |
| aligned prime + **mod-8 pin** (`p2`) needed | 4 222 263 | 2 474 017 | all | 0 |
| aligned prime + **decimal-tail coset** needed | 2 970 695 | 880 834 | all | 0 |
| **sumset** (unaligned prime), needs tail coset | 114 (prime leaves, in 24 of the 26 `decimal5_high` certs) | 114 | all | 0 |
| sumset without any pin | 0 occurrences | – | – | – |
| multiset lifts (partition/completeness) | 112 873 032 lifts | – | all | 0 |
| size leaves (empty by size) | 84 | – | all | 0 |

Observations. (i) The sumset kill occurs *only* as the final prime leaf (114 instances, never as an internal "rest" kill), and in every one of them the kill needs the tail coset (the plain sumset does not kill). (ii) For the `broad_pin2` stage (37 certs) the new ingredient is the mod-8 pin (1.1 M kills need it); for `decimal_full`, `decimal5_high`, `decimal_pilot` the tail coset (3.0 M kills). (iii) All 121 certificates have `K` odd (`t0 = 0`) and `qmin = 3`, so pin2 (`qmin ≥ 3`) is valid, `k = 3 ≤ qmin`, and the "divide by `2^{t0}`" subtlety is vacuous for the certificates themselves; it is exercised by the positive controls (t0 ∈ {0,1,3}, §3).

## 3. Soundness tests of the kill machinery (independent of the 121 certificates)

`test_F.py` (seeded, stdlib). These test the mathematics of §1 directly, not the certificates.

| test | what it checks | result |
|---|---|---|
| T1 | (a) children partition the parent: for random (M, f, group shapes) all labelled tuples mod fM reducing to the parent are enumerated exhaustively; the set of their sorted keys equals my lift set (no duplicates, none missing); `|Lift| = f·ΠC(f+h−1,h)`; the number of labelled tuples above a parent is `f^{F+1}` times the number below; 2000 random actual (distinct-position) points each lie in exactly one child | PASS (60 labelled-enumeration cases, 2000 point-in-one-child cases) |
| T2 | (b) sumset is a superset: for random classes, primes, moduli, actual points in the class (random `q = r + M·t`, distinct) satisfy `X mod p ∈ 𝒮(κ)` | PASS (12000 actual points, 200/400 sumsets proper subsets of Z/p) |
| T3 | (c)/(P2) pins hold on random domain points (`v2(X)=t0`, `X≡K mod 10^k`, `X/2^{t0} ≡ K/2^{t0} mod 8`, mod `E` = lcm-combined modulus); for random smooth targets `N=2^{t0}3^a7^w` placed in the equation, the true `(a mod A, w mod W)` is in the admissible pair set | PASS (1333 random domain points / smooth targets) |
| T4 | **positive controls**: ~42 random genuine solutions (random groups, `t0 ∈ {0,1,3}`, random pins valid for that `qmin`) — for every modulus in a list of 8–18 values (including multiples of 27, 7, 36, 252, 1008) and every prime `11 ≤ p < 500` (plus 9901, 333667, 52579, 999999000001, 73, 137, 101, 98641, 99990001 …), the class of the true solution is **never** killed (27687 (class,prime) tests; 0 wrong kills); the 3-adic and 7-adic signatures are consistent with the true exponents. On random *non*-solution classes the same machinery produces kills of all kinds (so the test is not vacuous): {'aligned/p2': 1136, 'aligned/plain': 8078, 'sumset/plain': 1720, 'sumset/p2': 3882, 'aligned/tail': 338, 'sumset/tail': 1035, 'aligned/both': 3} | PASS |
| T5 | (d) my DFS for `X = N` equals brute-force enumeration (1200 values, 1200 solutions, plus spurious-value checks) | PASS (1200 values, 1200 solutions compared with brute force) |

(An earlier, larger T4 run was cancelled for time; the reported T4 figures are the 3 completed seeds only. Sumsets with more than 3·10^6 residues are skipped by my checker with an explicit `OverflowError`; none of the 121 real certificates hits that cap.)

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
* Differences that are harmless: M's list `rest` is reordered in place (move-to-front); M's solution tuples are flat `(L, q_1…)` while mine are `[L, [group positions]…]`; M requires coefficients sorted by value and `c % 10 ≠ 0`, I only require distinct positive coefficients; M's tamper set consists of dimension-1 `scope=class` files.
* **I found no disagreement in mathematics, and no unsound step.**

**Differential tests (black-box agreement of the two kill procedures).** `diff_F.py` imports M's `Checker.killed(p, r, M)` and my `Cert.kills(p, cls, M)` and compares them on random valid parameters (random groups of sizes 1–7 slots, random odd-part `K` with `t0 ∈ {0,1,2,3,5}`, `qmin ≥ t0+1`, pin2 on/off when valid, `pin_digits ∈ {0,1,2,3}`, 5 random moduli from `{1,2,4,6,12,18,36,42,72,84,126,144,216,252,432,504,756,1008}`, 20 random classes each, 12 random primes each from a list including aligned and unaligned primes, 9901, 333667, 99990001, …): 5 seeds, **59978 comparisons, 59978 agreements, 0 disagreements** (kill/kill: 35258, survive/survive: 24720; 22 pairs skipped by my size cap).

**Verdict comparison on corrupted files.** On the 30 tamper files of §6 (`cmp_tamper.json`), M's `check_sym.py` and `check_sym_F.py` returned the same verdict on every file (including the informational vacuous cases).

**Decision.** There is no case where the two checkers disagree, so no case needing arbitration; both are consistent with my proofs. Differences in strictness (M rejects unsorted/non-unique group listings and `c % 10 = 0` coefficients, mine accepts them but none occur) do not affect any of the 121 certificates.

## 5. Coverage: configuration → slice → certificate (task 4)

`f_cover.py` (own code; E's `e_enum.py` used only as a cross-check).

1. **Model.** Digit strings `d_{L-1}…d_0` with digits in {1,2,3,4,6,7,8,9} (0 and 5 excluded since the product 14112 = 2^5·3^2·7^2 is nonzero and prime to 5). `n = (10^L−1)/9 + Σ (d_i−1)10^i`, so `9n = 10^L + K + Σ_{i≥3} A_i 10^i` with `K = 9·S_low − 1`, `S_low = Σ_{i<3}(d_i−1)10^i`, `A = 9(d−1)` ∈ {9,18,27,45,54,63,72}. Checked on **all 339 486 digit strings of length ≤ 9 with product 14112**: each lies in a configuration `(S_low, sorted far A's)` of my enumeration, and the identity holds exactly. (Lengths < 5 cannot reach product 14112; for `L ≥ 3` `n mod 1000 = 111 + S_low`.) The configuration key is unique per digit string. Configurations of target 14112: **1640**; my set equals E's exactly (`my config set == E's config set`).
2. **Slices.** For K and the free far multiset R, my recursion `slices(K,R)` decides positions p = 3,4,… in increasing order: stop when `p ≥ max(3, v2(K)+1)` (all free positions are then `≥ p > t0`); otherwise either position p holds digit 1 (continue) or one of the distinct free digits (fix: `K += A·10^p`, remove A from R). This is a partition of all placements. Demo (even K, i.e. odd S_low): `S_low = 1` (K = 8, t0 = 3) gives pieces `(8,(9,18),qmin 4)`, `(9008,(18,),5)`, `(189008,(),5)`, `(18008,(9,),4)`; `S_low = 105` (K = 944, t0 = 4) gives 13 pieces.
3. **Result for the 121 closed keys** (`summary.json["closed"]`):
   * all 121 keys are real configurations (also: all 331 baseline keys, closed + BUDGET, are real configurations);
   * **all 121 have S_low even, hence K = 9·S_low−1 odd, t0 = 0, and my recursion yields exactly ONE slice `(K, far multiset, qmin = 3)`** for each — there is *no v2 edge case* among the closed configurations (the 172 BUDGET configurations with odd S_low are the ones that would need them, and none was claimed closed);
   * for each of the 121 slices there is exactly one certificate in `highdim/sym/certs/*/` with the same `K`, group multiset (coefficient → multiplicity) equal to the far multiset, `qmin = 3 ≤` slice qmin, `scope=full`, `domain=unordered`, root = (all-zero mod 1), `qmin > v2(K)`, and **my checker returns PASS with no declared solution**;
   * my slice→certificate map equals M's `coverage_audit.json` map for **121/121**; the 121 certificates are pairwise distinct (max 1 configuration per file); 25 further certificate files in `certs/` (same four directories) are not used by any of the 121 closures (they are leftovers/other attempts; not relied on).
   * **Domains match.** Cert domain: pairwise distinct positions `3 ≤ q < L`, one slot per far digit, groups by *coefficient value* — this is the "unordered" domain, so all orderings of different far digits are covered at once (the ordered-domain hole that E found in `checknd` certificates does not occur). The slice domain: far digits at pairwise distinct positions `≥ 3`, `L >` all positions (the leading digit at position L−1 may itself be a far digit). Equal.
   * **L below the certificate floor.** A configuration with m far digits needs `L ≥ 3 + m ≥ 8`, while the certificate domain contains every `L ≥ 4`; so no point of these configurations lies below the certificate floor and no finite exception scan is needed for the 121 closures. (M additionally scanned to `Lmax = 21`.)
4. **Independent end-to-end consistency.** `f_scan.py`: all 11 119 028 numbers `2^i 3^j 7^k < 10^200` were enumerated and their digit products read from the decimal string: the only one with product 14112 is **33718272** (config `161|18,18,54,63`, 4 far digits — *not* among the 121). So no counterexample to the claim "no member in the 121 closed configurations" exists below 10^200. (A consistency check; the proof is the certificates.)
5. **Ledger status caveat (11 promoted keys).** 110 of the 121 keys have status `SLICE_COVER_CHECKED` in an `attack_*.json` ledger (decimal_full 71, broad_pin2 18, decimal5_high 15, decimal_pilot 11, with overlaps). The other **11** (`10|18,18,27,27,54,54`, `10|9,18,18,54,54,63`, `10|9,9,27,54,54,72`, `110|9,18,18,27,54,54`, `12|9,9,18,27,54,54`, `130|9,9,18,18,54,54`, `150|9,9,9,18,54,54`, `16|9,9,9,18,45,54`, `210|9,9,18,27,54,54`, `50|9,9,18,27,54,54`, `56|9,9,9,9,18,54`) are `BUDGET` in every stage ledger: the certificate file was completed just before the in-pipeline checker timed out and M promoted it after a standalone PASS (see the last PROVED paragraph of `notes/highdim_sym.md`). Because a file written at a timeout could in principle be truncated, I note explicitly that my checker verified these 11 files in full (completeness of the lift cover, reachability, every kill): all 11 PASS, so none is truncated or partial. The mapping used in the table below is `coverage_audit.json`'s, which I verified against my own slices.

| stage dir | certificates used by the 121 | PASS (mine) |
|---|---|---|
| `decimal_full` | 52 | 52 |
| `broad_pin2` | 37 | 37 |
| `decimal5_high` | 26 | 26 |
| `decimal_pilot` | 6 | 6 |
| **total** | **121** | **121** |

**Coverage conclusion: 121/121 configurations are covered by exactly one independently accepted certificate; no uncovered slice, no v2 edge case, no domain mismatch.**

## 6. Tamper tests (task 5)

`tamper_F.py`, `tamper2_F.py` build corrupted copies of real certificates (in `tamper/`) and run `check_sym_F`. Base certificates used: `decimal5_high/K1943_…` (contains sumset leaves; 450 588 lifts), `decimal_full/K5723_…` (tail kills, repeated residues; 9 290 lifts), `broad_pin2/K2087_…` (pin2 only). Unmodified bases: **ACCEPTED** (4/4). `cmp_tamper.py` also ran M's `check_sym.py` on every file (last column).

| tamper | modification | mine | first reason given | M's check_sym |
|---|---|---|---|---|
| `sumset_leaf_prime_swapped` | sumset leaf 295 prime 196482241(sumset/tail)->11 | **REJECTED** | leaf 295: prime 11 does not kill | FAIL |
| `sumset_leaf_class_shifted` | sumset leaf 295 residue shifted | **REJECTED** | node 291: lift (249, (35, 99, 228, 345), (349,), (36,)) mod 432 neither child nor killed | FAIL |
| `sumset_single_representative` | leaf 295: prime 41 kills if residue is taken as the exponent (single rep) but not over the full sumset | **REJECTED** | leaf 295: prime 41 does not kill | FAIL |
| `tail_pin_removed` | meta pin_digits 3 -> none (kills that need the coset must fail) | **REJECTED** | node 1: lift (2, (4, 4, 4), (2, 2)) mod 6 neither child nor killed | FAIL |
| `tail_pin_too_wide` | pin_digits=4 > min(3,qmin) (classic over-pin) | **REJECTED** | pin_digits out of range | FAIL |
| `tail_qmin_below_pin` | qmin=2 with pin_digits=3 (pin beyond minimum position) | **REJECTED** | pin2 requires qmin >= t0+3 | FAIL |
| `tail_K_plus_9000` | K += 9000 (same K mod 9 and mod 1000: only the other primes see it) | **REJECTED** | node 0: lift (0, (1, 1, 1), (1, 1)) mod 2 neither child nor killed | FAIL |
| `tail_K_plus_18000` | K += 18000 (same K mod 9 and mod 1000: only the other primes see it) | **REJECTED** | node 0: lift (0, (1, 1, 1), (0, 1)) mod 2 neither child nor killed | FAIL |
| `INFO_K_plus_1000` | INFORMATIONAL: K+=1000 changes K mod 9 => a=0 exact, impossible with the pin => vacuously closed | **ACCEPTED** |  | PASS |
| `INFO_pin2_flipped_with_tail` | INFORMATIONAL: pin2 off while tail k=3,t0=0 (tail already implies mod 8) | **ACCEPTED** |  | PASS |
| `pin2_removed_no_tail` | cert with pin2 only: pin2 -> false | **REJECTED** | node 0: lift (0, (1, 1, 1), (0, 1)) mod 2 neither child nor killed | FAIL |
| `pin2_qmin_too_small` | pin2 with qmin=2 < t0+3 | **REJECTED** | pin2 requires qmin >= t0+3 | FAIL |
| `multiset_child_deleted` | node 0: first child removed from c | **REJECTED** | node 0: lift (0, (0, 0, 0), (0, 0)) mod 2 neither child nor killed | FAIL |
| `multiset_child_duplicated` | node 0: duplicate child id | **REJECTED** | duplicate child class at 0 | FAIL |
| `multiset_child_not_a_lift` | child 1: one residue +1 (reduction mod parent changes) | **REJECTED** | duplicate child class at 0 | FAIL |
| `multiset_child_class_swapped` | child 1 given sibling 2 class | **REJECTED** | duplicate child class at 0 | FAIL |
| `multiset_rest_emptied` | node 0: rest primes removed | **REJECTED** | node 0: lift (0, (1, 1, 1), (1, 1)) mod 2 neither child nor killed | FAIL |
| `multiset_repeat_split_wrong` | node 1: one copy of a repeated residue moved | **REJECTED** | duplicate child class at 0 | FAIL |
| `ms_repeat_to_other_lift_4` | child 11: one of the equal residues 2 moved to the other lift 4 (still a lift of the parent) | **REJECTED** | node 2: lift (2, (2, 2, 4), (1, 2)) mod 6 neither child nor killed | FAIL |
| `ms_multiplicity_not_preserved` | child 11: one copy of repeated residue 2 replaced by 3 (reduction mod 2 changes) | **REJECTED** | node 2: lift (2, (2, 2, 4), (1, 2)) mod 6 neither child nor killed | FAIL |
| `ms_deep_child_deleted` | node 2: child 11 removed | **REJECTED** | node 2: lift (2, (2, 2, 4), (1, 2)) mod 6 neither child nor killed | FAIL |
| `ms_deep_rest_weak` | node 2: rest primes replaced by [101] | **REJECTED** | node 2: lift (2, (4, 4, 4), (3, 4)) mod 6 neither child nor killed | FAIL |
| `tail_qmin2_pin2off` | qmin=2 with pin_digits=3 and pin2 off (isolated over-pin: pin deeper than the smallest allowed position) | **REJECTED** | pin_digits out of range | FAIL |

Notes.
* **Required three** — a corrupted sumset-kill leaf (`sumset_leaf_prime_swapped`, `sumset_leaf_class_shifted`, and the targeted `sumset_single_representative`: a prime that would kill if each residue were treated as the exact exponent mod `d` — the classic over-optimistic sumset — but does **not** kill over the full sumset; the checker rejects it), a corrupted tail-coset (`tail_pin_removed`: kills that need the coset fail; `tail_pin_too_wide`/`tail_qmin_below_pin`/`tail_qmin2_pin2off`: the "pin deeper than the smallest position" error (k > min(3, qmin)) is rejected at the meta level — the last one isolates it from pin2; `tail_K_plus_9000/18000`: K changed in a way invisible to the mod-9/mod-1000 data, so only the other primes can notice — rejected), and a corrupted multiset child (`multiset_*` and `ms_*`: deleted child, duplicated child, child class swapped with a sibling, residue not reducing to the parent, a repeated residue pair split wrongly, a different genuine lift in place of the true one, `rest` primes emptied/weakened) — **all rejected**.
* Two informational cases are (correctly) **accepted**: `INFO_K_plus_1000` changes `K mod 9`, so `v3(X)=0` exactly, which is incompatible with the tail coset (`3^a7^w ≡ K/2^{t0} mod 1000` forces `a ≡ 3 mod 10`): the configuration is then closed vacuously by the pins; `K += 8` likewise makes the target non-representable mod 1000 (empty pair set). `pin2` toggled off while `k = 3`, `t0 = 0` is also accepted because the tail modulus 1000 already contains the mod-8 information. Both checkers agree on these.
* K-sensitivity of the checker was also verified positively: planting a genuine smooth solution (`K := 3^a7^w − X_0` for random placements) and keeping the same tree is **rejected** in 12/12 trials (the unlisted lift containing the planted solution is not killed), so the acceptance of the real certificates is not an artefact of leniency.
* M's own tamper directory consists of dimension-1 `scope=class` controls plus a few full trees; the dim-1/class files are outside my checker's scope by design (I reject `scope != full`) and are not used.

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


# PART B — scope extension: sym2 (M2), 398 further target-14112 configurations

Added after Part A. Same checker (`check_sym_F.py`, extended for dim-1 certificates = no coefficient groups, domain `L ≥ qmin`, and M2's flat solution lists), same proofs (§1). Files in `indep4/sym2/`. M2's ledger: 54 762 new certificates (+13 `scope=class` controls that I do not use), 398 configurations CLOSED (by M2's `dim` = number of far digits + 1: dim 4: 8, dim 5: 298, dim 6: 85, dim 7: 7).

## B0. Verdict for Part B

* **Kill types.** The decimal-tail coset and the mod-8 pin are **sound with the conditions below**, including for the `t0 = v2(K)` up to 31 and `qmin` up to 34 that occur in sym2. The sumset and prime-coset kills are as in Part A (**sound**). No unsound step found.
* **Certificates (sample).** 487 stratified-random sym2 certificates: **487 / 487 PASS** under my independent checker (115 001 256 lifts, each a child or killed).
* **Coverage (sample).** 62 randomly chosen closed configurations (stratified by M2's three coverage methods and dimensions): **62 / 62 COVERED** by my own slice recursion, using only certificates that my checker accepts (all **12 785** listed domain certificates of those 62 configurations were checked: 12 785 / 12 785 PASS). A 63rd configuration, `161|18,18,54,63` (the one containing the known member 33718272), was audited separately: covered, 302/302 certificates PASS.
* **Not done:** the remaining ≈ 335 closed configurations and ≈ 41 000 closure certificates were **not individually replayed**. Structural validity of all 54 764 full-scope metadata records was checked (B1). So what is *independently confirmed* is: the kill-type soundness (all certificates rely only on these), and a sample (487 certs, 63 configs / 13 000+ certs). Treat the other 398 − 63 = 335 closures as "supported by confirmed kill soundness + a clean random sample (0 failures in 13 000+ replayed certificates, 0 uncovered configurations in 63)", not as individually re-proved by me. A full replay would cost ≈ 0.55 CPU-hours per 1 000 certificates at the observed mean (≈ 2 s/cert), i.e. ≈ 24 CPU-hours for the 43 689 closure certificates; I did not run it.

## B1. Special scrutiny: the decimal-tail coset and the mod-8 kill (what congruence, on which domain, 2^{t0})

Let a certificate have constant `K` (`t0 = v2(K)`, `K0 = K/2^{t0}` odd), floor `qmin`, and domain 𝒟 = {points with all slot positions `q ≥ qmin`, pairwise distinct, `L > q`} (for dim 1: `L ≥ qmin`). Every point of 𝒟 has all of its positions **and `L`** `≥ qmin`.

1. **V2 (needed by both).** `qmin > t0` ⇒ `2^{t0+1} | 10^L, 10^q` ⇒ `v2(X) = t0` on all of 𝒟. Hence `Y = X/2^{t0}` is an *odd integer* equal to `3^a 7^w` if X is smooth. All 54 764 full-scope certificates satisfy `qmin > v2(K)` (checked, `sym2/meta_all.py`).
2. **Mod-8 kill (`pin2`).** Claim: on all of 𝒟, `Y ≡ K0 (mod 8)`. Proof: `qmin ≥ t0+3` ⇒ `2^{t0+3} | 10^L` and `| 10^q`, so `X ≡ K (mod 2^{t0+3})`; divide the congruence **once** by `2^{t0}` (both sides are multiples of `2^{t0}`): `Y ≡ K0 (mod 8)`. `3^a7^w mod 8` is a bijection from `(a mod 2, w mod 2)` to the odd residues, so the parities of `a` and `w` are *forced*; an exact exponent of the wrong parity is impossible; a free exponent moves in steps of 2 (coset of `⟨9⟩` / `⟨49⟩` at an auxiliary prime). Domain of validity: whole 𝒟, provided `qmin ≥ t0+3`. **All 45 670 pin2 certificates satisfy `qmin ≥ t0+3` (in fact `qmin = t0+3` exactly in every one)** — checked on all, not a sample. Without the floor the claim is false (e.g. `qmin = t0+1` gives `Y ≡ K0` only mod 2).
3. **Decimal-tail kill (`pin_digits = k = 3` in all sym2 certificates).** Claim: on all of 𝒟, `X ≡ K (mod 10^3)`, hence `Y ≡ K0 (mod 5^3)` and `Y ≡ K0 (mod 2^{max(3 − t0, 0)})`. Proof: `qmin ≥ 3` ⇒ `10^3 | 10^q, 10^L` for every term, so `X − K ≡ 0 (mod 2^3 5^3)`. Both `X` and `K` are multiples of `2^{t0}` and `gcd(2^{t0}, 5^3) = 1`, so the `5^3` part transfers to `Y − K0` unchanged, while the `2^3` part becomes `2^{max(3−t0,0)}` after dividing **once** by `2^{t0}` (vacuous when `t0 ≥ 3`). Domain: all of 𝒟, provided `k ≤ min(3, qmin)` — all sym2 certificates satisfy it (checked on all). **`t0 ≥ 3` holds in 52 874 of the 54 762 tail certificates, so for them the tail kill is purely the 5-adic congruence `Y ≡ K0 (mod 125)`**; its 2-adic strength then comes only from pin2. Pairs `(a mod A, w mod W)` with `A = ord_E(3)`, `W = ord_E(7)` for `E = lcm(8·[pin2], 2^{max(3−t0,0)}) · 125` (E = 125 when `t0 ≥ 3` and no pin2, E = 1000 when pin2); the combination of the two congruences is legitimate because both are congruences for the same number `K0`.
4. **Using the pairs at a prime p** (aligned or sumset): `Y mod p ∈ ⋃_{(α,β) admissible} 3^{α}7^{β}·⟨3^A (if a free), 7^W (if w free)⟩`; exact signatures select `α ≡ a0`, `β ≡ w0`; lower bounds on free exponents remove nothing from the image of an infinite arithmetic progression in the finite group `F_p^*`. For `p` unaligned the left-hand side is `2^{−t0}·(sumset)`; `2^{−t0}` is applied exactly once.
5. **Classic errors, and how they are excluded/tested.** (i) *Pin deeper than the smallest position*: `k > qmin` or `pin2` with `qmin < t0+3` — both rejected by both checkers at meta level and by my tamper tests (§6), and absent from all 54 764 metas. (ii) *Dividing by `2^{t0}` twice*: would use `2^{max(3−2t0,0)}` — weaker, not unsound; the opposite error (not dividing: modulus `2^3` on `Y`) **is unsound**, and `mutation_F.py` shows it loses true solutions (for `t0 ≥ 2`, 85–114 of ~220–265 planted true solutions per `t0`: table below), while the correct modulus never does. (iii) *Using the pins for classes outside the domain* — not possible: the pins are properties of the whole domain 𝒟, not of subclasses.

`mutation_F.py` (qmin = max(3, t0+1), no pin2; true solutions planted):

```
t0= 1  true solutions 256 | correct modulus 5^3*2^max(3-t0,0): true pair missing 0 | WRONG modulus 5^3*2^3 on K/2^t0: true pair missing 0
t0= 2  true solutions 266 | correct modulus 5^3*2^max(3-t0,0): true pair missing 0 | WRONG modulus 5^3*2^3 on K/2^t0: true pair missing 98
t0= 3  true solutions 262 | correct modulus 5^3*2^max(3-t0,0): true pair missing 0 | WRONG modulus 5^3*2^3 on K/2^t0: true pair missing 104
t0= 4  true solutions 265 | correct modulus 5^3*2^max(3-t0,0): true pair missing 0 | WRONG modulus 5^3*2^3 on K/2^t0: true pair missing 114
t0= 6  true solutions 258 | correct modulus 5^3*2^max(3-t0,0): true pair missing 0 | WRONG modulus 5^3*2^3 on K/2^t0: true pair missing 108
t0=12  true solutions 222 | correct modulus 5^3*2^max(3-t0,0): true pair missing 0 | WRONG modulus 5^3*2^3 on K/2^t0: true pair missing 85
```

6. **Positive controls with large `t0`.** `T3`/`T4` re-run with `t0 ∈ {0,1,2,3,4,5,7,10,12}` (and `{1,…,12,20,31}`), `qmin = (t0+3 or 3) + {0..4}`, random pin2/tail validity: T3x 2288 random domain points / smooth targets all PASS (pins hold; true exponent pair is in my admissible set); T4x 16 genuine-solution instances (completed seeds only; slower seeds were cancelled for time) × all moduli/primes tested = 6032 (class, prime) tests, **0 wrong kills** (classes containing a true solution are never killed, with pins on).

## B2. Checker run on a stratified random sample of sym2 certificates

`sym2/select_sample.py 7` — strata = (dimension) × (M2's kill-dependency set) → 36 strata, ≤ 9 random certificates each (205), plus extras: 80 sumset-dependent, 60 with `t0 ≥ 10`, 40 dim-1, and 25 per stage directory (floor72, high_positions72, broad8, cache_recovery8; precomputed24: 2). Total **487** (all `scope=full`). Run: `sym2/run_py.py sym2/sample_7.json sym2/out_sample7` (14 workers).

| item | result |
|---|---|
| certificates | 487 |
| PASS / FAIL / TIMEOUT | **487 / 0 / 0** (one certificate initially FAILed on a bug of *my* checker — dim-1 size leaf with `R = 0` — which I fixed; test T5 re-run; the rerun passes) |
| by dimension (1,2,3,4,5,6,7,8) | 143, 71, 39, 103, 92, 26, 10, 3 — all PASS |
| `t0 = 0` / `1–3` / `4–9` / `≥ 10` | 18 / 143 / 221 / 105 — all PASS |
| M2-declared dependency (all PASS): prime_coset / decimal_tail_coset / mod8_parity / unaligned_sumset / exact_size | 487 / 485 / 346 / 162 / 43 |
| lifts enumerated | 115001256 (killed: 114915800) |
| leaves | 1303 = 741 prime leaves + 562 size leaves |
| brute box points / hits | 23203 / 0 |
| declared solutions | 1 (the dim-1 collision slice `K245744_q5_cnone`: L = 5, n = 38416 = 2^4·7^4, digit product 576 ≠ 14112 — a slice of the impossible "four far digits fixed in two positions" kind that M2 reports as `impossible_fixed_collision_branches`; not used by any cover) |

Verified kills (minimal pin variant that suffices, my classification): aligned prime — plain 96036937, needs mod-8 10514601, needs tail 8303283, needs both 60979; **sumset** (all in prime leaves, 741 instances): plain 46, mod-8 15, tail 608, both 72. So in sym2 the sumset kill occurs in a plain form too, and *all* its occurrences were re-derived by my independent code.

(M2's "dependency" labels are certificate-level flags: 99 of the 485 sampled certificates labelled `decimal_tail_coset` use no kill that actually needs the tail coset (all their kills are plain or mod-8). Labels are therefore upper bounds on the dependency; harmless.)

## B3. Coverage mapping on a random sample of sym2 configurations

`sym2/select_cfg.py 3` → 62 closed configurations (seed 3), stratified by M2's coverage method and dimension: {('distinct_fixed_positions', 5): 2, ('distinct_fixed_positions', 6): 14, ('distinct_fixed_positions', 7): 6, ('original_enlarged_cover', 4): 8, ('original_enlarged_cover', 5): 14, ('original_enlarged_cover', 6): 2, ('position_partition', 5): 5, ('position_partition', 6): 10, ('position_partition', 7): 1}. `sym2/f_cover2.py` (own code, independent of M2's cover code): for configuration `(S_low, far multiset R0)` it starts at `(K0 = 9·S_low − 1, R0, p = 3)` and recursively either (i) stops if a **checker-accepted** certificate with `K' = K`, groups = `R`, `qmin ≤ p` exists in the configuration's listed domain (for `R = ∅` the certificate may have `qmin ≤ 201`: the points with `L < qmin` are the finite smooth-lattice part, which I scanned independently to `10^200`: only member 33718272), or (ii) splits position `p`: "no far digit" or "one of the distinct remaining far digit values fixed at `p`" (`K += A·10^p`), and continues at `p+1` — a partition of all placements that never fixes two digits at one position. A branch with no matching certificate up to the largest listed `qmin` is reported UNCOVERED.

| item | result |
|---|---|
| configurations | 62 |
| **COVERED / UNCOVERED** | **62 / 0** |
| (method, dim) | {('distinct_fixed_positions', 5): 2, ('distinct_fixed_positions', 6): 14, ('distinct_fixed_positions', 7): 6, ('original_enlarged_cover', 4): 8, ('original_enlarged_cover', 5): 14, ('original_enlarged_cover', 6): 2, ('position_partition', 5): 5, ('position_partition', 6): 10, ('position_partition', 7): 1} |
| certificates listed for them / examined by my checker | 12 785 / 12 785 — **all PASS** |
| slices used by my recursion / listed | 10976 / 12785 (the 1 809 listed-but-unused certificates are in five configurations — 896 in `57|9,18,54,54`, 416 in `633|9,18,18,54`, 313 in `161|18,27,45,54`, 127 in `761|9,18,18,54`, 57 in `605|9,27,45,54` — presumably collision slices or redundant refinements; the other 57 configurations use every listed certificate; no slice was missing) |
| configurations with `K0` even (odd `S_low`; v2 edge cases at positions 3…`t0`) | 45 of 62 (`t0(K0)` up to 9), all covered |
| max `t0` / max `qmin` among used slices | 31 / 34 |
| declared solutions in used certificates | 0 |
| special: `161|18,18,54,63` (the closure that contains member 33718272) | COVERED: 120 slices, 302/302 certificates PASS; the member (L = 8, far digits at positions 3,5,6,7) lies in the finite region and is exactly the unique member found by the independent scan |

Domain match: certificates are `domain=unordered, scope=full, root = all-zero mod 1`, groups by coefficient value ⇒ every ordering of distinct far digits is covered by construction (the same property that fixes E's ordering hole); my recursion fixes explicit digit values at explicit positions, so orderings are enumerated by my code, not assumed from M2's `ordering_audit`.

## B4. Part B — final counts

| | count |
|---|---|
| sym2 closed configurations claimed | 398 |
| kill-type verdicts (tail, mod-8, sumset, prime-coset) | sound (conditions B1) — all conditions verified on **all** 54 764 full-scope metadata records |
| sampled certificates replayed independently | 487 / 487 PASS; plus 12 785 / 12 785 coverage-sample certificates PASS and 302 / 302 for the member configuration = **13 574 PASS, 0 FAIL** |
| sampled configurations independently covered | 63 (62 random + 1 special) / 63 |
| configurations individually re-proved by me | 63 of 398 |
| remaining 335 closures | not individually replayed (supported by the above; full replay ≈ 25 CPU-h) |

Files (Part B): `sym2/select_sample.py`, `sym2/sample_7.json`, `sym2/run_py.py`, `sym2/out_sample7/`, `sym2/select_cfg.py`, `sym2/cfg_sample_3.json`, `sym2/cover_certs_3.json`, `sym2/out_cover3/` (+ `cover_report.json`), `sym2/f_cover2.py`, `sym2/cfg_member.json`, `sym2/out_member/`, `sym2/meta_all.py`, `mutation_F.py`, `assemble2_F.py`, `check_sym_F.py` (extended; `check_sym_F_v1_backup.py` is the version used for Part A — the 121 results were produced by v1; the changes (dim-1, R ≥ 0, flat solutions) do not affect groups ≥ 1 certificates and I re-ran two Part-A certificates with the new version: PASS).
