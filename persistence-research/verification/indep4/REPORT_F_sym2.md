

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

6. **Positive controls with large `t0`.** `T3`/`T4` re-run with `t0 ∈ {0,1,2,3,4,5,7,10,12}` (and `{1,…,12,20,31}`), `qmin = (t0+3 or 3) + {0..4}`, random pin2/tail validity: T3x 2288 random domain points / smooth targets all PASS (pins hold; true exponent pair is in my admissible set); T4x 16 genuine-solution instances × all moduli/primes tested = 6032 (class, prime) tests, **0 wrong kills** (classes containing a true solution are never killed, with pins on).

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
