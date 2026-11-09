# Theory: attacking the 11-step conjecture

**Conjecture (the hypothesis).** Every positive integer reaches a single digit in
at most 11 iterations of "replace n by the product of its decimal digits".
Equivalently: no integer has persistence ≥ 12. The record is
277777788888899 → … → 0 in exactly 11 steps (smallest such number, OEIS A003001).

Notation: `Π(n)` = product of decimal digits of n (`Π(0)=0`); `P(n)` = persistence
(`P(n)=0` for n<10; `P(n) = 1 + P(Π(n))` for n ≥ 10). "7-smooth" = of the form
`2^a·3^b·5^c·7^d`. `dc(m)` = number of decimal digits of m; `len(m)` = minimum
number of digits from {1,…,9} whose product is m.

---

## 1. Termination (easy direction)

**Lemma 0.** `Π(n) < n` for all n ≥ 10. Hence every chain reaches a single digit
and `P(n) < ∞`; the open question is only whether `sup_n P(n)` is bounded.

*Proof.* Let n have D ≥ 2 digits with leading digit d. Then `Π(n) ≤ d·9^{D−1} <
d·10^{D−1} ≤ n`. ∎

So chains strictly decrease. The conjecture is a *uniform bound* statement.

## 2. Master reduction: the problem lives on 7-smooth numbers

**Theorem 1.** An integer with `P(n) ≥ 12` exists **iff** a 7-smooth integer with
`P(m) ≥ 11` exists.

*Proof.*
(⇒) Take n with P(n) ≥ 12, n ≥ 10. Every decimal digit has prime factors ≤ 7,
so `m := Π(n)` is 7-smooth (F4), and `P(m) = P(n) − 1 ≥ 11`.

(⇐) Let `m = 2^a·3^b·5^c·7^d` with P(m) ≥ 11 (m ≥ 10, so (a,b,c,d) ≠ 0). Let n be
the integer whose decimal digits are a `2`s, b `3`s, c `5`s, d `7`s
(`prime_digit_expansion`). Then `Π(n) = m`, so `P(n) = 1 + P(m) ≥ 12`. ∎

**Corollary 1.1.** The conjecture ⟺ **every 7-smooth number has P ≤ 10**.

This is the structural heart of the attack: the search space collapses from all
integers to the 4-dimensional lattice (a,b,c,d). It is also *constructive*: any
7-smooth persistence-11 number immediately yields an explicit persistence-12
number.

## 3. The length domain

**Lemma 2.** For `m = 2^a·3^b·5^c·7^d`: `len(m) = c + d + len23(a,b)`, where
`len23(a,b)` = min number of digits from {2,3,4,6,8,9} with product `2^a·3^b`.

*Proof.* In any digit factorization of m, digits divisible by 5 are exactly {5}
and by 7 exactly {7}; each contributes one factor 5 (resp. 7) and no 2s/3s. So
any factorization uses ≥ c digits `5`, ≥ d digits `7`, and the remaining digits
(from {2,3,4,6,8,9}) must produce `2^a·3^b`, hence ≥ len23(a,b) of them. Both
bounds are achieved simultaneously. ∎

`len23` satisfies the Bellman recursion over digit vectors 2→(1,0), 3→(0,1),
4→(2,0), 6→(1,1), 8→(3,0), 9→(0,2); implemented as `len23_table` and verified
against branch-and-bound (`src/test_core.py`). Also `len23(a,b) ≥ max(⌈a/3⌉,⌈b/2⌉)`,
so `len23(a,b) ≤ D` forces `a ≤ 3D`, `b ≤ 2D` — the DP table is finite.

## 4. Search completeness (the D-digit theorem)

**Definition.** `𝓜_D := { 2^a·3^b·5^c·7^d : len23(a,b) + c + d ≤ D }` = all
7-smooth numbers that are a product of ≤ D digits.

**Theorem 3.** If every `m ∈ 𝓜_D` has `P(m) ≤ 10`, then **no n < 10^D has
persistence ≥ 12**. Conversely, if some `m ∈ 𝓜_D` has `P(m) ≥ 11`, an explicit
persistence-12 number is `prime_digit_expansion(a,b,c,d)`.

*Proof.* Let n < 10^D with P(n) ≥ 12; n has ≤ D digits, so `m := Π(n)` is a
product of ≤ D digits, i.e. `len(m) ≤ D`, and m = 2^a·3^b·5^c·7^d is 7-smooth.
By Lemma 2, `len23(a,b)+c+d ≤ D`, so m ∈ 𝓜_D; but `P(m) = P(n)−1 ≥ 11`,
contradicting the hypothesis. The converse is Theorem 1(⇐). ∎

So an exhaustive sweep of 𝓜_D is a *decision procedure* for "persistence-12
below 10^D": it either proves the bound or hands us a counterexample.
(`src/lattice_search.py`, subagent A.) This is also how the record computations
were done — OEIS A003001 calls the elements of 𝓜_D "reduced numbers". Verified
lineage of D-bound results (notes/literature.md): Sloane 1973 → D=50, Carmody
2001 → D=233, Diamond 2010 → D=333, Perez–Styer 2015 (peer-reviewed) → D=1500,
Chaffin 2016 → D=20585, Peters 2023 → no persistence-12 below 2.67×10^30000.

## 5. Structure of a minimal counterexample

**Lemma (merge monotonicity).** Let X, Y be equal-size digit multisets with
`sorted(X) < sorted(Y)` (lexicographic on the sorted digit strings) and
`∏X = ∏Y`. Then for any digit multiset R, `sort(R∪X) < sort(R∪Y)`.
*Proof sketch.* Induction on |R| by stripping the common minimum; verified
exhaustively for all X, Y, R with |X|=|Y| ≤ 4, |R| ≤ 4, digits 2–9
(`src/verify_merge_lemma.py`). ∎

**Lemma 4.** Let `n* = min{ n : P(n) ≥ 12 }` (exists iff the conjecture fails).
Then the digit multiset of n*:
1. contains no 0 (P would be 1) and no 1 (deleting a 1 preserves Π, hence P,
   and lowers the value);
2. is sorted ascending (sorting preserves Π and lowers the value);
3. contains at most one 2, one 3, one 4, one 6 — via same-product
   replacements with fewer digits ({2,2}→4, {3,3}→9) or equal digits but
   smaller sorted string ({4,4}→{2,8}, {6,6}→{4,9}) — each producing a smaller
   number with the same P, contradicting minimality;
4. contains no pair {2,3} (→6), {2,4} (→8), {3,4} (→{2,6}), {3,6} (→{2,9}),
   {4,6} (→{3,8}) — same-product replacements, by the merge lemma.

*Consistency:* every record setter satisfies these (e.g. 277777788888899 =
2,7⁶,8⁶,9²). The much stronger folklore constraint "all digits after the second
are 7,8,9" (Sloane) involves chain depth, not just minimality; we cite it
(literature.md) rather than reprove it. ∎

## 6. Conditional resolution of the full conjecture

**Theorem 5.** Suppose:
- **(A)** [computed] every `m ∈ 𝓜_D` has `P(m) ≤ 10` for some D; and
- **(B)** [hypothesis] every 7-smooth number with **more than C decimal digits**
  contains the digit 0, where `C` satisfies `D ≥ ⌈C·log₉10⌉ + 1`.

Then no integer has persistence ≥ 12.

*Proof.* Suppose P(n) ≥ 12; let `m = Π(n)` (7-smooth, P(m) ≥ 11).
- If `dc(m) > C`: by (B) m has a digit 0, so `Π(m) = 0` and `P(m) = 1`, whence
  `P(n) = 2` — contradiction.
- If `dc(m) ≤ C`: then `m ≤ 10^C`, so `len(m) ≤ log₉(m) ≤ C·log₉10`, i.e.
  `len(m) ≤ ⌊C·log₉10⌋ ≤ D−1`... more precisely `len(m) ≤ ⌊C·log₉10⌋+1 ≤ D`, so
  m ∈ 𝓜_D and (A) gives `P(m) ≤ 10`, whence `P(n) ≤ 11` — contradiction. ∎

(`log₉ 10 = ln10/ln9 ≈ 1.048`.)

**Status of the two inputs.** (A) is a finite computation — subagent A's sweep.
(B) is not new to this project: it is **Conjecture 1 of de Faria & Tresser
(arXiv:1307.1188)** — "there exists k₀(q) such that for all k ≥ k₀(q), the base-q
expansion of any product of k digits greater than 1 has at least one digit equal
to zero" — here quoted in our dc-form. Chaffin's A003001 comment already verifies
it *computationally* for reduced numbers (7-smooth) with dc between 141 and
20000 ("All p(n) between 10^140 and 10^20000 have a persistence of 1, meaning
they contain a 0 digit"); the zero-digit sweep (subagent B) re-verifies this
independently and pins down the largest zero-free 7-smooth number. Proving (B)
in general is open — even the case `2^a` alone is the classical "86-conjecture"
(OEIS A007377: 2^86 is the largest known zero-free power of 2; "it is an open
problem of long standing to show that 86 is the last term"). **The entire open
problem is thereby isolated to: "do large 7-smooth numbers contain the digit 0?"**
— a question about digits of powers `2^a3^b5^c7^d` (see §8).

Note (B) can be weakened: it suffices that for every 7-smooth m with dc(m) > C
*some* element of its Π-chain hits a 0 digit within 9 steps; and the threshold
interplay is flexible (larger computed D buys a weaker (B)).

### Theorem 5′ (assembled from this project's computations)

Given the three ingredients below, no integer has persistence ≥ 12:

- **(i)** [lattice sweeps — both done] every `m ∈ 𝓜_525` has `P(m) ≤ 10`
  (agent A: all 19,210,237,201 points; lead: all 15,813,314,001 points of
  𝓜_500 — identical verdicts, `results/lattice_results.md`,
  `results/lead_lattice_results.md`);
- **(ii)** [zero-free sweep, exhaustive] every 7-smooth m with
  `141 ≤ dc(m) ≤ 500` contains the digit 0;
- **(iii)** [hypothesis — the only open input] every 7-smooth m with
  `dc(m) > 500` contains the digit 0.

*Proof.* Suppose P(n) ≥ 12; let m = Π(n) (7-smooth, P(m) ≥ 11).
- len(m) ≤ 525 ⟹ m ∈ 𝓜_525 ⟹ (i) gives P(m) ≤ 10 ⟹ P(n) ≤ 11. Contradiction.
- len(m) > 525 and dc(m) ≤ 500: the bridge lemma `len(m) ≤ (ln10/ln5)·dc(m) + 2
  = 1.4307·dc(m) + 2` (optimal factorizations use 8s for 2s and 9s for 3s; the
  worst value-per-digit is the lone digit 5) gives dc(m) ≥ ⌈(526−2)/1.4307⌉ = 367,
  so (ii) applies: m contains 0, P(m) = 1, P(n) = 2. Contradiction.
- dc(m) > 500: (iii) applies, same contradiction. ∎

So the residual open problem is exactly (iii) — de Faria–Tresser Conjecture 1 —
pushed beyond 500 digits, where heuristics give an expected count of zero-free
7-smooth numbers ≈ Σ_{dc>500} (2.2·dc)³·0.9^dc / 57.2 ≈ 0 (the empirical zero-
free counts already collapse to zero by dc = 140).

## 7. Why 12 steps should be impossible (heuristic)

A persistence-12 chain needs, for i = 0…10, the chain element Πⁱ(n) to be
≥ 10 with **no zero digit** (a single 0 anywhere in Π¹…Π¹¹ kills the chain by
step i+1 ≤ 11) *and* the digit products to stay large enough that the digit
count never collapses below 2 digits. Two independent suppressions compound:

1. **Zero-freeness:** random L-digit numbers are 0-free with probability
   0.9^L. Over a chain of digit counts L, ≈0.618L, … this costs 0.9^{≈2.6L}.
2. **Shrink-rate tail:** the digit count multiplies by ≈0.618 per step *on
   average* (E[log₁₀ d] = log₁₀(9!)/9 ≈ 0.618 for uniform nonzero digits), so a
   chain dies after ≈ 4.44·log₁₀(L) steps. Surviving 11 steps requires the
   product to beat the typical shrink at several consecutive levels — an
   upper-tail event at each level, compounding to roughly 10^{−3}–10^{−6}.
   This is *why* record setters have digits 7,8,9 (Sloane's structural law):
   survival requires persistently large digits.

**Calibration (measured, `results/heuristic_calibration.md`, 10⁶ samples):** random
L-digit integers have persistence 1 (a zero digit) with probability → 1; even among
hand-made 0-free starts the max persistence *falls* with L (10 at L≤20, 5 at L=30,
3 at L=45, 2 at L≥65), and persistence ≥ 11 was never observed in any cell
(450 000 samples). The two suppressions are empirically brutal: at L=15 — where
the genuine record 277777788888899 lives — P(P ≥ 11 | 0-free) < 2×10⁻⁵, and the
survivors are exactly the numbers whose digits stay 7/8/9-heavy down the chain.

**Conclusion of the heuristic:** the expected total number of persistence-12
integers is astronomically below 1 — but turning this into a theorem requires
control of digit statistics of `2^a3^b5^c7^d`, which is open (§8).

## 8. What a full proof would need — the honest gap

Theorem 5 reduces everything to the de Faria–Tresser zero-digit statement (§6,B).
Even the special case `2^a` — "2^86 is the last zero-free power of 2" — is "an
open problem of long standing" (OEIS A007377). Known results point the *other*
way: Senge–Straus (1973) / Stewart (1980) prove `2^a` has **unboundedly many
nonzero** decimal digits (effective, via Baker's theory) — control in the
direction of forcing zeros is not available. Proving digit-frequency statements
for powers runs into the standard obstruction: no equidistribution theorem for
digits of `2^a3^b5^c7^d` is known (compare: normality of `(3/2)^n`, Mahler's
problems).

On the persistence side, the strongest known results are: BCGN (arXiv:2110.04263,
2021) — the conjecture holds when the chain ends at an **odd** digit
(Δ ∈ {1,3,7,9} ⇒ P ≤ 1; Δ = 5 ⇒ P ≤ 5), leaving even targets 2,4,6,8 (and 0)
open behind their 2-adic "Conjecture 2"; and Fonga (arXiv:2608.27802, v1,
28 Aug 2026, **unrefereed**) — proves that 2-adic conjecture in full generality
(explicit uniform v_p bounds in any base b ≥ 3, p | b), reducing each nonzero
even terminal digit to a finite computation that has **not been carried out**
("carrying out the full computation lies beyond the scope of this paper"). The
only claimed complete proof (Sghiar 2017, IOSR-JM) disposes of its final case
with "(Testé sur ordinateur)" and is cited by no one. Full citations and
verbatim quotes: notes/literature.md.

**Bottom line.** What this project proves outright:
- The reduction to 7-smooth numbers (Theorem 1) — with proof (independently
  re-derived here; the community's version is the "reduced number" formalism of
  A003001 / de Faria–Tresser).
- No n < 10^D has persistence ≥ 12, for the D reached by the lattice sweep
  (Theorem 3 + `results/lattice_results.md`) — machine-verified, and
  cross-validated against Chaffin's published frontier (our independently found
  P=10 7-smooth number 2⁴·3²⁰·7⁵ is exactly Chaffin's "largest p(n) with
  P(p(n)) = 10").
- The structural theory of counterexamples — Theorems A–F of
  **`notes/pure_math.md`** (zero-trap families, certified threshold cascade
  τ₁…τ₁₀, rigid min-lex form of the minimal counterexample with ≤ 2 digits
  outside {7,8,9}, the 164-multiset level-0 sieve, chain closure at dc ≤ 822,
  and the precise Diophantine form of the remainder). Certificates:
  `results/tau_table_lead.json`, `results/minlex_certificate.md`,
  `results/level0_multiset_counts.json`.
- The conditional resolution (Theorem 5): conjecture ⟸ zero-digit statement
  about 7-smooth numbers + our sweep.
What remains open: the digit statement itself.
