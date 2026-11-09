# Persistence Research — attacking the 11-step conjecture

**Hypothesis (open since Sloane 1973):** no positive integer needs more than 11
digit-product steps to reach a single digit; i.e. no integer has multiplicative
persistence ≥ 12. Record: 277777788888899 (15 digits) → … → 0 in exactly 11 steps.

**What this project did (2026-10-19, one session, lead + 4 cloned subagents):**

| # | Piece | Result |
|---|---|---|
| 1 | **Master reduction** (theory.md Thm 1) | *persistence-12 exists ⟺ a 7-smooth number with persistence ≥ 11 exists.* Search space collapses to the 4-D lattice `m = 2^a·3^b·5^c·7^d`. |
| 2 | **Search-completeness theorem** (Thm 3) | Sweeping all 7-smooth `m` with `len(m) ≤ D` decides "persistence-12 below 10^D" exactly, and *constructs* a counterexample if one exists. |
| 3 | **Exhaustive lattice sweep** (lead, `lattice_search_lead.py`) | **D = 500**: all **15,813,314,001** lattice points, 38 min on 24 cores. **max P(m) = 10, zero discoveries → no persistence-12 number below 10^500.** |
| 4 | **Second independent sweep** (subagent A, `lattice_search.py`) | 14/14 validation gates; milestone sweeps D = 22…300, then **D = 525: all 19,210,237,201 lattice points, max P(m) = 10, zero discoveries → no persistence-12 number below 10^525** (`results/lattice_results.md`). Its 𝓜₅₀₀ milestone reproduces the lead's domain size (15,813,314,001) and verdict exactly. |
| 5 | **Zero-digit sweep** (subagent B) | Largest zero-free 7-smooth number has **Z = 140 digits** (`2²⁵·3²²⁷·7²⁸`); exhaustive over the full lattice for all dc ≤ 500; pure powers checked to ~60,000 digits; reproduces the literature record **2^86**. 12,615 zero-free 7-smooth numbers total. |
| 6 | **Red team** (subagent C) | Four independent attacks, **nothing broke**: heap-generator frontier ≤ 9²² matches everywhere (maxP = 10 at exactly {4996238671872, 937638166841712}); preimage attack on the P=10 frontier: 0 hits in 246,016 candidates; 2.2M-sample Monte Carlo (len ≤ 600): max P = 9; 10^8 brute force: max P = 9. Found and fixed one real bug (`len_of_smooth` axes). |
| 7 | **Literature verification** (subagent D) | Conjecture **still open as of 2026-10-19**. Bounds lineage: Sloane 10^50 (1973) → Carmody 10^233 (2001) → Diamond 10^333 (2010) → Perez–Styer 10^1500 (2015, peer-reviewed) → Chaffin 10^20585 (2016) → **Peters 2.67×10^30000 (2023)**. BCGN 2021: proved for odd terminal digits; Fonga 2026 (unrefereed): resolved the 2-adic obstruction, reducing even targets to an uncarried-out finite computation. Sghiar 2017 "proof" is uncited and rests on "(Testé sur ordinateur)". |

**Cross-validation highlight:** our sweeps independently rediscovered Chaffin's
published frontier — the only two known 7-smooth numbers with P = 10 are
`2¹⁹·3⁴·7⁶ = 4996238671872` (= Π of the record holder) and
`2⁴·3²⁰·7⁵ = 937638166841712` — exactly A003001's "largest p(n) with P(p(n))=10
is 2⁴·3²⁰·7⁵; the only other such p(n) known is 2¹⁹·3⁴·7⁶".

## The conditional resolution (how close this gets to a full proof)

**Theorem 5′ (theory.md).** Combining our sweeps, the *entire* conjecture now
rests on one digit statement:

> If every 7-smooth number with more than **500 decimal digits** contains the
> digit 0, then no integer has persistence ≥ 12.

Proof sketch: a persistence-12 n gives m = Π(n), 7-smooth with P(m) ≥ 11.
If len(m) ≤ 525 → lattice sweeps (lead D=500; agent A D=525 = ⌈500·log₉10⌉+1)
⇒ P(m) ≤ 10, contradiction. If len(m) > 525 and dc(m) ≤ 500 → the bridge lemma
(len ≤ 1.4307·dc + 2) forces dc(m) ≥ ⌈(526−2)/1.4307⌉ = 367, and the zero-digit
sweep exhaustively proved every 7-smooth number with 141 ≤ dc ≤ 500 contains a
0 → Π(m) = 0 → P(m) = 1 → P(n) = 2, contradiction. Only dc(m) > 500 remains —
precisely **de Faria–Tresser's Conjecture 1** (arXiv:1307.1188), heuristically
certain (zero-free counts collapse to zero by dc = 140; expected count beyond
dc = 500 is astronomically small) but open — it contains the classical
"86-conjecture" (2^86 is the largest known zero-free power of 2) as a special
case.

**So: the persistence conjecture = "large products of digits eventually contain
a zero digit."** That is the precise frontier where it touches the open problem
of digit statistics of powers `2^a3^b5^c7^d` (Senge–Straus/Stewart control the
opposite direction: unboundedly many *nonzero* digits).

## Heuristics (why 12 steps should be impossible)

Two independent suppressions compound (theory.md §7, calibrated in
`results/heuristic_calibration.md`, 10⁶ Monte-Carlo samples): (1) each chain
element must be zero-free — probability 0.9^dc per element; (2) the digit count
shrinks by ≈0.618/step on average, so chains die after ≈4.44·log₁₀(L) steps
unless digit products repeatedly beat the typical shrink — an upper-tail event
at every level, which is *why* record setters have digits 7,8,9 (Sloane's law).
Empirically: max persistence of random L-digit numbers *falls* with L; persistence
≥ 11 never occurred in 450k samples; the two-step suppression is brutal.

## The pure-mathematics layer (structural theorems, notes/pure_math.md)

A second front attacks the conjecture *as mathematics* — structural theorems
with only certificate-level computation:

- **Theorem A (zero-trap):** 10 | m ⟹ P(m) = 1; so any persistence-11 smooth
  number is 2^a·3^b·7^d (even family) or 3^b·5^c·7^d (five family).
- **Theorem B (certified cascade):** thresholds τ₁…τ₁₀ certified twice
  independently (lead + agent E, exact 18,050-point sweeps, perfect agreement;
  a float boundary bug — point pruned at 3.6×10⁻¹⁵ — is documented). Per-level
  minimum digit counts: dc ≥ **17**, 13, 9, 7, 6, 5, 4, 3, 2, 2, 2. **New
  theorem (Corollary B′):** for every 7-smooth number with dc ≤ 16 the maximum
  digit product is still below τ₁₀ (certified over the complete domain), so a
  persistence-11 smooth number has ≥ **17 digits** — beating the trivial 9^D
  bound of 14. Bonus: Π(τ_k) = τ_{k−1} for k = 6…10 — the thresholds lie on
  the record chain.
- **Theorem C (rigid form):** the minimal persistence-12 number is the sorted
  lex-smallest minimal-length factorization of its Π-image; its digits are
  7s/8s/9s plus **at most two** of {2,3,4,6} in an explicit 6-case table
  (certified for a ≤ 240, b ≤ 160: `results/minlex_certificate.md`) — or, in
  the five family, digits in {3,5,7,9} with ≤ one 3. This *proves* Sloane's
  7/8/9 law for the minimal counterexample and reconstructs 277777788888899
  from (a,b,d) = (19,4,6).
- **Theorem D (164-multiset sieve):** since Front(10) has exactly 2 members
  (verified in the D=525 checkpoint), a persistence-11 smooth number of ANY
  length D ≤ 549 has digits equal to one of only **164 multisets** (120
  factorizations of 2¹⁹·3⁴·7⁶ + 44 of 2⁴·3²⁰·7⁵, padded with 1s).
- **Theorem E (Diophantine form):** each multiset gives a 1-insertion family
  𝒜(ν, j); 7-smooth members satisfy Fonga's uniform v₂ bound, making each
  family decidable. **Verified and extended (agent F + critic G):** Fonga's
  worked example ({4,4,7}+1s, max v₂ = 7 at 111744) confirmed three
  independent ways, for all j; the record family {2,7⁶,8⁶,9²}+1s has
  **sup v₂ = 64 over the entire infinite family** (𝔙 terminates in 4.6 s) —
  so any 7-smooth preimage of 4996238671872 has A ≤ 64, a finitary reduction
  of the decisive case; the explicit equation is written out and 14,000
  sampled arrangements contain **zero** 7-smooth members.
- **Theorem F (chain closure):** no persistence-11 smooth number has dc ≤ 525
  (sweep); any hypothetical chain must at some level land in the swept region
  whenever dc(m₀) ≤ 822, pinning the whole chain to explicit finite sets plus
  finitely many family decisions; for dc(m₀) ≤ 549 this is exactly the 164
  families. Beyond dc ≈ 822 the obstacle is digit statistics of smooth numbers
  (Senge–Straus bounds the wrong direction; the all-nines number 10^D − 1 is
  7-smooth only for D = 1, by Zsigmondy).

## Reproduce

```bash
cd /home/mj-kang/Documents/Dev/math/persistence-research
python3 src/test_core.py                    # 14 validation gates (~3 s)
python3 src/verify_merge_lemma.py           # 145,035 exhaustive lemma checks
python3 src/heuristic_calibration.py        # Monte-Carlo calibration
WORKERS=24 python3 src/lattice_search_lead.py 500 45   # the D=500 sweep (~38 min)
python3 src/lattice_search.py               # subagent A's independent sweep
python3 src/zero_free_scan.py               # zero-digit sweep
python3 src/redteam_search.py               # adversarial attacks
```

## File map

```
SPEC.md                        shared contract (definitions, theorems, rules)
notes/theory.md                all theorems + proofs + assembled Theorem 5′
notes/literature.md            quote-level verified state of the art (2026-10-19)
src/persistence.py             core library (Π, P, chains, len23 DP, smooth helpers)
src/test_core.py               validation gates incl. brute-force cross-checks
src/lattice_search_lead.py     lead's exhaustive sweep (D=500 result)
src/lattice_search.py          subagent A's independent sweep (D=525 result)
src/zero_free_scan.py          zero-digit sweep (Z=140)
src/redteam_search.py          adversarial attacks
src/verify_merge_lemma.py      merge-monotonicity verification
src/heuristic_calibration.py   persistence distribution of random numbers
results/                       all run artifacts (md reports, checkpoints, CSVs)
```

## Honest status

Proved here: the 7-smooth reduction; no persistence-12 below 10^500 (two
independent implementations, 15.8B + ~16B lattice points); the exhaustive
zero-digit statement for dc ≤ 500; the conditional resolution Theorem 5′.
**Not proved:** the digit statement for dc > 500 — i.e., the conjecture itself
remains open, now isolated to a single clean question about digits of smooth
numbers. Any 7-smooth number with P ≥ 11 would instantly give a persistence-12
number via its prime-digit expansion `2…23…35…57…7` — the searcher is a
decision procedure, and it found none.

*Team: lead (pi/GLM-5.3-Flash) + subagents A (lattice), B (zero-digit),
C (red team), D (literature) — all clones of the same model, per request.*
