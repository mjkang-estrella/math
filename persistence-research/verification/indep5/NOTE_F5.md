# NOTE_F5 — checker F5: decimal-tail coset pins with deep `pin_digits = k <= qmin`

Auditor: review sub-agent F5 (extension of `verification/indep4/check_sym_F.py`).
Everything is in `verification/indep5/`; stdlib only; every Python run uses
`bash -c 'ulimit -v 6000000; python3 -I …'`.  `check_sym_F_base.py` is a
**byte-identical copy** of `indep4/check_sym_F.py` (sha256-verified by
`regress_F5.py`) and is used as the regression oracle; nothing outside
`indep5/` was written, nothing was committed.  `verification/highdim/sym5/`
was **not read** until the checker and all tests below were finished.

## 0. What F5 changes

`check_sym_F5.py` differs from `check_sym_F.py` in exactly three places (all
marked `# [F5]`):

1. **Meta validation.**  `pin_digits = k` is accepted for `1 <= k <= qmin`
   (was `k <= min(3, qmin)`).
2. **The admissible-set computation.**  The naive enumeration of all
   `(a mod A, w mod W)` pairs (`pairs`, cost `A*W ~ 24*25^(k-1)` exponentiations
   mod `E`) is replaced by an exact coset/lattice solver (`_pinstruct`,
   `_solve_gx`, `_solve_free`, `_solve_pair`, `_adm`), described in §3.
   The *semantics* — the set of allowed residues at an auxiliary prime — is
   unchanged; test T1 verifies set-equality against the old code on 24003
   random cases, T2f at `k = 5` where the old enumeration is still feasible.
3. **`kill_variant`.**  The union of cosets `⋃ 3^ae 7^be·H` is represented as a
   single coset `rep·⟨gens⟩`; the membership test `pow(y, nU, p) == T` replaces
   `pow(y, nH, p) in img`.  One exponentiation per sumset element, as before.

Everything else — V2, (SIG), (AL), (SS), size leaves, the brute box, `Eset`,
the tree walk — is untouched.

## 1. Soundness of the pin for `k <= qmin` (the two edge cases)

Setting as in REPORT_F §0/§6: domain points have all positions `q` and `L`
`>= qmin`; `X = 10^L + Σ c_i 10^{q_i} + K`, `t0 = v2(K)`, `K0 = K/2^{t0}` odd.

**Claim (tail pin, deep `k`).**  If `1 <= k <= qmin` then on the whole domain
`X ≡ K (mod 10^k)`, hence `Y := X/2^{t0}` (an odd integer by (V2), since
`qmin > t0`) satisfies

    Y ≡ K0 (mod 5^k)      and      Y ≡ K0 (mod 2^{max(k−t0, 0)}),

i.e. `3^a 7^w ≡ K0 (mod E)`, `E = 2^{max(k−t0,0)} · 5^k`.

*Proof.*  Every term `10^q` with `q >= qmin >= k`, and `10^L` with `L > q >= k`
(`L >= qmin` for dimension 1), is divisible by `10^k = 2^k 5^k`; so
`X − K ≡ 0 (mod 2^k 5^k)`.  Both `X` and `K` are multiples of `2^{t0}`
(positions `>= qmin > t0`), so write `X = 2^{t0} Y`, `K = 2^{t0} K0` and divide
the congruence `2^{t0}(Y − K0) ≡ 0 (mod 2^k 5^k)` **once** by `2^{t0}`: the
`5^k` part transfers unchanged (`gcd(2^{t0},5)=1`), the `2^k` part becomes
`2^{max(k−t0,0)}`.  ∎

**Edge case `k` vs `t0`.**

* `t0 >= k`: the 2-adic part is **vacuous** (`max(k−t0,0) = 0`); the pin is the
  pure 5-adic congruence `Y ≡ K0 (mod 5^k)`.  Note `2^k | X − K` still holds
  but dividing once consumes it exactly: `Y − K0` is then only known `≡ 0 mod 1`.
  Dividing *twice* (`2^{k−2t0}`) would be a *weaker* claim — unsound only in the
  opposite direction; *not* dividing (`2^k` against `Y`) is the unsound error,
  exercised by the T4b discriminator (a checker that uses `K` in place of `K0`
  and exponent `k` in place of `k−t0` wrongly "kills" every lift and accepts a
  certificate containing a planted true solution; F5 rejects it, §5/T4b).
* `t0 < k`: the 2-part is `2^{k−t0}`; this is a genuine constraint on the odd
  `Y` and is combined with the 5-part into the single modulus `E` (both are
  congruences for the *same* number `K0`, so CRT combination is legitimate).
  When `pin2` is also set, `Eset` already uses `e2 = max(3, k−t0)`; the mod-8
  congruence (`qmin >= t0+3`, enforced) and the tail congruence agree on `K0`,
  so their combination is again exact.

**Edge case `k = qmin` (deepest legal pin).**  Every position satisfies
`q >= qmin = k` and `L > q >= k` (`L >= qmin = k` in dimension 1), so the pin
holds on the *whole* domain — the same argument as for `k <= min(3,qmin)`, with
no additional hypothesis.  `k > qmin` would be unsound (a position `q < k`
contributes a term not divisible by `10^k`) and is rejected at meta level and
by T4a.

**Vacuous degeneracies** (all verified in T2/T1): if `5 | K0` then
`3^a 7^w ≡ K0 (mod 5^k)` has no solution — the old code found `P = ∅` and
killed; F5 returns "empty admissible set" and kills identically.  Same for
`E ∈ {1, 2}` (congruence vacuous, allowed set `⟨3,7⟩`, exactly as the old
`E = 1` branch) and for even `τ` with a 2-part modulus (defensive; cannot occur
since `K0` is odd).

## 2. Orders for large `k` (the task's brief, corrected)

`ord_{5^k}(3) = 4·5^{k−1}` (3 is a primitive root mod 5^k).  The brief's claim
that the same holds for 7 is **not correct**: `v5(7^4 − 1) = 2`, so
`ord_{5^k}(7) = 4·5^{max(k−2,0)}` (4 for `k <= 2`).  Nothing in the old code
depended on the closed form (`order()` computed it exactly); F5 needs the
exact orders only through the CRT decomposition, and T2a verifies the identities
by direct computation.  Mod `2^j`: `ord_{2^j}(3) = 2^{j−2}` for `j >= 3`
(`⟨3⟩ = {units ≡ 1, 3 mod 8}`), and `ord_{2^j}(7) | 2^{j−2}` (equality can fail:
`ord_{16}(7) = 2`, `ord_8(7) = 2`); both checked in T2a.

## 3. The structured admissible set (what replaced the pair enumeration)

The pin congruence `3^a 7^w ≡ K0 (mod E)`, `E = 2^{e2} 5^{e5}`, is solved
*exactly* (no relaxation, no weakening):

* **5-part** (`e5 >= 1`; if `5 | K0` the set is empty).  3 is a primitive root,
  so with `s5 = dlog_3(7)` and `u5 = dlog_3(K0)` (Pohlig–Hellman mod `4·5^{e5−1}`:
  `x mod 4` via `3^{5^{e5−1}}`, `x mod 5^{e5−1}` digit-by-digit via `3^4`) the
  congruence is the linear relation `a + s5·w ≡ u5 (mod A5)`, `A5 = 4·5^{e5−1}`.
* **2-part.**  `e2 <= 1`: vacuous.  `e2 = 2`: `7 ≡ 3 (mod 4)`, relation
  `a + w ≡ u2 (mod 2)`.  `e2 >= 3`: `⟨3⟩ = {units ≡ 1,3 mod 8}` of order
  `A2 = 2^{e2−2}`, and `7 = −3^{s2}` with `s2 = dlog_3(−7)` (bit-by-bit, since
  `3^{2^{j−3}}` has order 2).  Hence `3^a 7^w = (−1)^w 3^{a+s2·w}`, and the
  congruence forces the **sign** `w ≡ wpar (mod 2)` (`wpar` from `K0 mod 8`;
  `K0 mod 8 ∈ {1,3} → wpar = 0` and target `K0`; `{5,7} → wpar = 1`, target
  `−K0`, which lies in `⟨3⟩`) together with `a + s2·w ≡ u2 (mod A2)`.
* **Solving the system.**  With `w` ranging over the CRT-combined class
  `w ≡ w* (mod Mw)` (from the sign parity and the compatibility
  `(s2−s5)w ≡ u2−u5 (mod gcd(A5,A2))` of the two relations for `a`), `a` is an
  affine function of the free parameter `t`: `a ≡ g0 + gt·t (mod A)`,
  `A = lcm(A5, A2)`.  The solution set is exactly
  `(a_p, w_p) + ⟨(gt, Mw), (A, 0)⟩` — a coset of a rank-2 lattice.
* **Exact exponents.**  If the signature fixes `a = a0` (resp. `w = w0`), the
  exponent is substituted as a *constant* and the remaining single-variable
  congruence `7^w ≡ K0·3^{−a0} (mod E)` (resp. `3^a ≡ K0·7^{−w0}`) is solved by
  the same CRT-dlog machinery (`_solve_gx`); the solution set is `x* + M·Z`
  with `M` the exact period.  Both exact: a single membership check
  `3^{a0} 7^{w0} ≡ K0 (mod E)`.

**Why this equals the old union of cosets.**  The old code's allowed set is
`⋃_{(α,β)∈P'} 3^{ae} 7^{be} H` with `H = ⟨3^A, 7^W⟩ ⊂ F_p^*`; since
`H = {3^{iA} 7^{jW}}`, this is exactly `{3^a 7^w (mod p) : (a mod A, w mod W) ∈
P'}`, i.e. the image under `(a,w) ↦ 3^a 7^w (mod p)` of the solution set of the
same congruence system (exact signatures select the same sub-coset as the
substitution above).  F5 computes that image as `rep · ⟨3^{ga}7^{gw} mod p⟩`,
so the two are the *same subset of F_p^* pointwise*; the membership tests
(`y^{nH} ∈ img` vs `y^{nU} = rep^{nU}`, with `|H| = nH` and `|⟨gens⟩| = nU`)
are the same criterion.  Negative exponents in the coset add nothing (the
lattice contains `(A,0)`, `(0,W)`-type shifts).  Verified empirically:

* **T1** — 24003 random cases `(E, K0, sg, p)` over all `E = 2^{e2}5^{e5} ≤ 2·10^5`
  shapes (`e2 ≤ 6, e5 ≤ 5`, all four exact-signature combinations, `K0`
  sometimes divisible by 5, primes 11…97 and 9901): the allowed residue sets of
  old and new are **equal** in all cases (0 mismatches).
* **T2f** — the same at `k = 5` (`E = 2^{e2}·5^5`), where the old enumeration is
  still feasible: equal in all cases.

**Performance.**  Cost per `(E, sg)` is `O(k)` small exponentiations (the dlogs,
cached per `E`) plus two `order()` calls per prime; per sumset element one
moderation, as before.  No `A·W` enumeration anywhere; `k = 34` (`E = 2^34·5^34`,
`A ≈ 2^82`) is routinely handled (T2d).  On the regression sample F5 is
somewhat *faster* than the old checker.

## 4. Positive controls (true solutions with deep pins are never killed)

* **T2d (unit level).**  For `k ∈ {4,5,6,8,10,14}` and `t0 ∈ {0,1,3,k−1,k}`
  (both sides of the `k`–`t0` edge, and `pin2` combinations), a random true
  exponent pair `(a,w)` is made *admissible by construction* (`K0 ≡ 3^a 7^w mod
  E`, made odd when needed) and the residue `3^a 7^w (mod p)` must lie in F5's
  allowed set for 9 primes — it always does (0 violations in all runs).  The
  representative satisfies the pin and every generator is a pseudo-unit
  (`3^{ga}7^{gw} ≡ 1 mod E`); T2e additionally checks the allowed set equals
  `rep·⟨gens⟩` *exactly* (by explicit subgroup enumeration) for deep `k`.
* **T3 (certificate level).**  Valid certificates with `pin_digits = qmin` deep
  pins (dim 2, root → mod 2, all lifts killed by rest primes, brute box clean,
  independently re-enumerated) are **accepted** by F5, and the same file with
  the pin removed is **rejected** — the deep pin is load-bearing, not vacuous.
  Cases include `t0 = 0`, `t0 = 1`, `t0 = 3 < k = 5 < qmin = 7`, `t0 = k−1`,
  and `pin2` + deep tail combined.
* **T4b/T4c (planted solutions).**  Genuine smooth points (`X = 2^{t0}3^a7^w`,
  `v2(K) = t0` exact) planted in *undeclared* lifts of deep-pin certificates at
  `L >= 12` (invisible to the `L <= 11` brute box, which stays clean): F5
  **refuses to kill** the planted lift (the certificate is rejected, the planted
  lift named), while a checker that forgot to divide out `2^{t0}` kills it and
  wrongly accepts; at kill level, the planted class is never killed by F5 for
  any prime `11..199` and always killed by the forgot-to-divide variant.

## 5. Test inventory and results

All in `indep5/`, seeded, stdlib only (`test_F5.py`, `tamper_F5.py`,
`regress_F5.py`, builder `certkit.py`).

| test | what | result |
|---|---|---|
| T1 | allowed-set equality F5 vs `check_sym_F_base`, 24003 comparisons over all small `E` shapes | PASS (0 mismatches) |
| T2a | order identities `ord_{5^k}(3)=4·5^{k−1}`, `ord_{5^k}(7)=4·5^{max(k−2,0)}`, `ord_{2^j}(3)=2^{j−2}`, `ord_{2^j}(7)\|2^{j−2}` | PASS |
| T2b | `_dlog3_5k` / `_dlog3_2j` round trips (k ≤ 8, j ≤ 12) | PASS |
| T2c | `_solve_gx` solution sets vs brute force (exact period, exact set) | PASS |
| T2d | deep-k invariants + true point never excluded (k up to 14, all `t0` edges) | PASS |
| T2e | allowed set `= rep·⟨gens⟩` exactly (deep k, small p) | PASS |
| T2f | differential at `k = 5` vs old enumeration | PASS |
| T3 | 7 valid deep-pin certificates accepted; pin removal rejected; brute box independently clean | PASS |
| T4a | `pin_digits > qmin` (4 shapes) rejected at meta level | PASS |
| T4b | 4 planted smooth points, `t0 ∈ {1,2,3}`, deep pins (incl. `k = qmin = 11`): F5 rejects naming the planted lift; forgot-divide checker wrongly accepts; kill-level discriminator over primes 11..199 | PASS |
| T4c | 3 planted smooth points, `t0 = 0` (pure 5-adic deep pin) | PASS |
| T5 | regression: 50 certificates from `highdim/sym2/certs/` and `highdim/sym4/certs/`, full JSON verdicts of F5 and the unmodified checker identical (result, problems, claimed, brute, stats) | PASS (50/50 identical) |

## 6. The `sym5` deep-pin run (final step, after all tests above were frozen)

`verification/highdim/sym5/deep_pin_certs.txt` lists **12262** certificates in
three stages: `pin4_10` (78, `k = qmin = 4`), `pin5_30` (4638, `k = qmin = 5`),
`pin6_60` (7546, `k = qmin = 6`); `t0 = v2(K)` spans 0…26 (so both the
`t0 >= k` vacuous-2-part and `t0 < k` regimes occur), dims 1…8.  The run
(`run_F5_deep.py`, 10 workers, per-process 6 GiB cap, brute `L <= 11`):

| stage | PASS | other |
|---|---|---|
| pin4_10 | 78/78 | — |
| pin5_30 | 4638/4638 | — |
| pin6_60 | 7537/7546 | 6 FAIL `MemoryError`, 3 ERROR (died before JSON) |
| **total** | **12253/12262** | 9 resource-limited |

The 9 exceptions are all large dim-6/8 trees with tiny `K` (20M+ lifts) that
exhaust the 6 GiB process cap.  Three facts establish they are **resource
cap artifacts, not verdicts and not F5 regressions**:

1. The unmodified checker (`check_sym_F_base.py`) **exceeds 2400 s** on every
   one of the 9 (it is still enumerating `A·W ~ 24·25^5` pin pairs); F5 reaches
   the lift phase in 108–168 s and fails only at the memory cap.
2. The `MemoryError` originates in `sumset` — **pre-existing, byte-identical**
   code in both checkers (each level is materialised before the 3·10^6 cap
   check fires) — and propagates up the lift recursion; none of F5's new code
   appears in the traceback.
3. Rerun at a 30 GiB cap, F5 **verifies all 9**: each returns `PASS` with empty
   `problems` (`bigmem_results.txt`; largest: `K1889_q6_…`, dim 8, 20 847 354
   lifts, `rest_ok: 20847354`, ~7 min).  The base checker cannot verify any of
   them at any memory within hours (it never finishes enumerating the pin
   pairs `A·W ~ 24·25^5`).

So under the standard 6 GiB cap the verdict is **12253/12262 PASS** with the
other 9 reported as "could not verify (memory)"; with a 30 GiB cap F5 verifies
**12262/12262**.  In no case did F5 report a mathematical rejection: no
certificate in the list was found invalid.

## 7. Scope

F5 certifies exactly the claim of REPORT_F §0 with the pin range widened to
`k <= qmin`; nothing else about the certificates or the coverage argument is
re-derived here.  The other agent's `sym5/` work was not read before this note,
the checker and the tests were frozen.
