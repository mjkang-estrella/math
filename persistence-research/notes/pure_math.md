# Pure-mathematics attack: the structure of a would-be counterexample

Prerequisites: notes/theory.md (Π, P, 7-smooth, 𝓜_D, Theorems 1–5).
Here we develop the *structural* theory — no large computation, only theorems
plus three small certificate-level verifications (§3, §5, §6), each small enough
to be checked by hand-augmented scripts and emitted as explicit certificates.

Notation: dc(m) = #decimal digits of m; s(m) = digit sum; F = digit multiset;
Π(m) = ∏F; len(m) = min #digits (1–9) with product m; τ_k = min{7-smooth m :
P(m) ≥ k}; for m = 2^a3^b5^c7^d write the exponent 4-vector (a,b,c,d).

---

## Theorem A (zero-trap; the two families)

If 10 | m then P(m) = 1. Hence any 7-smooth m with P(m) ≥ 2 satisfies
**a·c = 0** (m = 2^a·3^b·7^d, the *even family*, or m = 3^b·5^c·7^d, the
*five family*).

*Proof.* 10 | m ⟺ the last decimal digit is 0 ⟹ Π(m) = 0 ⟹ P(m) = 1 + P(0) = 1.
For 7-smooth m, 10 | m ⟺ a ≥ 1 and c ≥ 1 (2 and 5 are the only primes giving
the factors 2·5 = 10… precisely: v₂ and v₅ of m are a and c). ∎

So a persistence-11 smooth number m₀ lies in one of two families (when a = c = 0
the two descriptions coincide — m = 3^b·7^d belongs to both, harmlessly). This
is the sharp form of the pruning used by the zero-digit sweep. [Critic G:
verified by trial division over all small (a,b,c,d) and all 7-smooth m < 10⁶.]

## Theorem B (certified threshold cascade)

**Certified thresholds** (results/tau_table_lead.json; all 7-smooth m ≤ τ₁₀
swept over 18,050 exact-integer-filtered lattice points, max P = 10 attained
only at τ₁₀; strict monotonicity verified):

| k | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|----|
| τ_k | 10 | 25 | 49 | 378 | 2688 | 27648 | 338688 | 4478976 | 438939648 | 4996238671872 |

(Verification note: a naive float log-budget *excludes* (19,4,0,6) by
3.6×10⁻¹⁵ — the sweep must carry an ε-slack and filter exactly in integers;
this boundary bug is documented here and in the certificate.)

**Structural bonus:** Π(τ_k) = τ_{k−1} for k = 6,…,10 — the thresholds lie on
the record chain 277777788888899 → τ₁₀ → τ₉ → τ₈ → τ₇ → τ₆ → τ₅ (then 768 ≠
τ₄ = 378: the coincidence ends at level 5).

Let m₀ → m₁ → … be the Π-chain of a 7-smooth m₀ with P(m₀) ≥ 11. Then every
mᵢ is 7-smooth (theory.md F4) and P(mᵢ) ≥ 11 − i, so

  (B1)  mᵢ ≥ τ_{11−i}   and   dc(mᵢ) ≥ ⌈log₉ τ_{10−i}⌉   for i = 0,…,10,

the second because mᵢ₊₁ = Π(mᵢ) ≤ 9^{dc(mᵢ)}. This alone gives dc(m₀) ≥ 14
(9¹³ = 2.54×10¹² < τ₁₀ ≤ 9¹⁴), but the *certified digit-statistics bound is
sharper*:

**Corollary B′ (dc(m₀) ≥ 17).** Over all 7-smooth m with dc(m) = D ≤ 16, the
MAXIMUM digit product is below τ₁₀ (results/level0_maxpi_certificate.json:
max Π = 5.6×10⁹ at D = 12, 2.4×10¹⁰ at 13, 1.2×10¹¹ at 14, 4.3×10¹² at 15,
3.9×10¹² at 16 — all < τ₁₀ = 4.996×10¹²; the first D with max Π ≥ τ₁₀ is 17).
Since P(m₀) ≥ 11 forces Π(m₀) ≥ τ₁₀, **a persistence-11 smooth number has at
least 17 digits.** Agent E's independent digit-sum test agrees (no 7-smooth
number with dc ≤ 14 has digit sum ≥ 114; results/level_feasibility.json), and
zero direct Front(10) hits occur for dc 10…30 — an independent
cross-validation of the D=525 sweep by a different method. The deeper levels
keep the combined bounds:

| level i | m₀ | m₁ | m₂ | m₃ | m₄ | m₅ | m₆ | m₇ | m₈ | m₉ | m₁₀ |
|---------|----|----|----|----|----|----|----|----|----|----|-----|
| dc(mᵢ) ≥ | **17** | 13 | 9 | 7 | 6 | 5 | 4 | 3 | 2 | 2 | 2 |

Moreover, by AM–GM applied to the digits of mᵢ, with s_i = s(mᵢ), D_i = dc(mᵢ):

  (B2)  s_i ≥ D_i · τ_{10−i}^{1/D_i},

a *lower bound on the digit sum at every level*. At the tight levels this is
very rigid at the new minimum: if D₀ = dc(m₀) = 17 then s(m₀) ≥
17·(4.996×10¹²)^{1/17} = 94.93, i.e. **s(m₀) ≥ 95 of a maximum 153 — the
total deficit Σ(9 − d) over the 17 digits of m₀ is at most 58** (digits
average ≥ 5.59; at most nine digits ≤ 3 since 10×6 = 60 > 58). (Deeper levels
are looser: a 13-digit m₁ needs s(m₁) ≥ 13·τ₉^{1/13} = 60.1, deficit ≤ 56.)
The full allowed-deficit-profile enumeration is a finite object (§3).
[Critic G verified the original D = 14 arithmetic, including the {3,3,9¹²}
product-exclusion; the statement is restated at the certified minimum
D₀ = 17 of Corollary B′.]

**Remark (deficit 0 impossible).** Δ(m) = 0 would mean m = 10^D − 1 (all
nines). By Zsigmondy's theorem, 10^n − 1 has a primitive prime divisor q ≡ 1
(mod n) for every n ≥ 2 (the exceptions (a,b,n) = (2,1,6) and a+b a power of
two do not occur for (10,1,n)); since 10^D−1 = 9·R_D with R_D coprime to 10,
7-smoothness of R_D forces all primes of R_D into {3,7}, but a primitive
divisor q ∈ {3,7} needs n | q−1, i.e. n | 6, and R_2 = 11, R_3 = 3·37,
R_6 = 3·7·11·13·37 are not 7-smooth. Hence **10^D − 1 is 7-smooth only for
D = 1**, so every 7-smooth m with dc ≥ 14 has Δ(m) ≥ 1.

## Theorem C (rigid form of the minimal counterexample)

Suppose a persistence-12 number exists and let n* = min{n : P(n) ≥ 12},
m₀ := Π(n*) (7-smooth, P(m₀) ≥ 11). Then:

1. n* is the **sorted, lex-smallest, minimal-length digit factorization of m₀**.
   *Proof.* Any n' < n* with Π(n') = m₀ has P(n') = P(n*) ≥ 12, contradicting
   minimality; so n* is the minimal preimage of m₀. Fewer digits ⟹ smaller
   number; equal digits ⟹ sorted arrangement is smallest; equal length ⟹
   lex-smaller sorted multiset is smaller. ∎

2. **(even family)** If m₀ = 2^a·3^b·7^d then the digits of n* are
     {7^d} ∪ F(a,b), where F(a,b), the sorted lex-smallest minimal-length
     factorization of 2^a·3^b, is explicitly:
       a≡0 (mod 3), b≡0: {8^{a/3}, 9^{b/2}}                     (0 small)
       a≡1, b≡0:         {2, 8^{(a−1)/3}, 9^{b/2}}             (1 small: 2)
       a≡2, b≡0:         {4, 8^{(a−2)/3}, 9^{b/2}}             (1 small: 4)
       a≡0, b≡1:         {3, 8^{a/3}, 9^{(b−1)/2}}             (1 small: 3)
       a≡1, b≡1:         {6, 8^{(a−1)/3}, 9^{(b−1)/2}}         (1 small: 6)
       a≡2, b≡1:         {2, 6, 8^{(a−2)/3}, 9^{(b−1)/2}}      (2 small: 2,6)
   In all cases **at most two digits lie outside {7,8,9}**.

3. **(five family)** If m₀ = 3^b·5^c·7^d then the digits of n* are
   {5^c, 7^d, 9^{⌊b/2⌋}} ∪ ({3} if b odd) — digits in {3,5,7,9} with at most
   one 3.

*Proof of 2.* Any minimal-length factorization of 2^a·3^b has length
len23(a,b); the candidate above has exactly that length (each digit is
length-efficient: 8 carries 2³, 9 carries 3², and the remainder digits are the
unique length-preserving completions; the a≡1,b≡1 case *shortens* {2,3} to {6},
and a≡2,b≡1 cannot be shortened below ⌊a/3⌋+⌊b/2⌋+2). Lex-minimality within
each length class is a finite case check per residue class (digit swaps like
{4,9}↔{6,6}, {2,9}↔{3,6}, {2,8}↔{4,4} all favour the displayed form — verified
exhaustively in §5). The bound "≤ 2 digits outside {7,8,9}" then reads off the
table. Consistency: for m₀ = Π(277777788888899) = 2¹⁹·3⁴·7⁶ the formula gives
{2, 7⁶, 8⁶, 9²} — exactly the record holder's digits. ∎

**Consequence.** The smallest persistence-12 number is fully parametrized by
(a,b,d) (even family) or (b,c,d) (five family) — the same lattices the sweeps
enumerate — and *any* persistence-12 candidate's canonical minimal form has
digits in {7,8,9} up to ≤ 2 exceptions (even family). This is Sloane's 7/8/9
law, now proved from first principles for the minimal counterexample.

**Consequence (explicit parametrization).** Combining C with A: the smallest
persistence-12 number, if it exists, is

  n*(a,b,d) = sort( {7^d} ∪ F(a,b) )   (even family), or
  n*(b,c,d) = sort( {5^c, 7^d} ∪ G(b) ), G(b) = {9^{⌊b/2⌋}} ∪ ({3} if b odd)

for the 5-family — a **3-parameter family with closed-form digit strings**, in
bijection with 7-smooth m₀. Π(n*) = m₀ holds by construction, so P(n*) ≥ 12 ⟺
P(2^a·3^b·7^d) ≥ 11: the search reduces exactly to the lattice sweeps, but now
with the candidate digit *strings* explicit — e.g. for (a,b,d) = (19,4,6) this
reconstructs the record holder 277777788888899 (verified computationally).

## Theorem D (the level-by-level feasibility sieve — sharp form)

The binding constraint at level 0 is not merely ∏F ≥ τ₁₀ (a value test) but
**∏F ∈ Front(10)** — the product must itself be a persistence-10 7-smooth
number. By the D=525 sweep (checkpoint verified: exactly 2 members with
P = 10, zero with P ≥ 11 among all 19,210,237,201 points), Front(10) =
{4996238671872 = 2¹⁹·3⁴·7⁶, 937638166841712 = 2⁴·3²⁰·7⁵} whenever dc(m₁) ≤ 525.
The digit multisets of m₀ are therefore (factorization of one target into
digits 2…9) ∪ {1ʲ}:

- 2¹⁹·3⁴·7⁶ has exactly **120** non-1 digit-multiset factorizations (six 7s
  forced; the 2/3-part enumerated over the exponent equations
  c₂+2c₄+c₆+3c₈ = 19, c₃+c₆+2c₉ = 4), minimal factorization 15 digits — the
  record setter 277777788888899;
- 2⁴·3²⁰·7⁵ has exactly **44**, minimal 17 digits.

**Corollary: for every D ≤ 549, a persistence-11 smooth number with D digits
has digits equal to one of only 164 multisets** (padded with 1s to length D),
and m₀ is then an arrangement of one of them. The weak value-test counts
(exact enumeration, results/level0_multiset_counts.json) are larger — 157
(D=14), 4,628 (15), 34,076 (16), 132,932 (17), 361,595 (18), 785,574 (19) —
but the 164-multiset bound holds at *every* length. Each of the 164 requires
a 7-smooth arrangement: none exists for dc ≤ 30 (subagent C's preimage
attack); dc 31–549 is the 1-insertion family decision of Theorems E–F, open
per Fonga and heuristically empty.

## Theorem E (the Diophantine form of the final gap; 1-insertion families)

Fix the multiset F(a,b) of Theorem C.2 (say the even family). The preimages n
of m₀ = 2^a·3^b·7^d with exactly the digit multiset {7^d} ∪ F(a,b) plus j
inserted 1s form the family 𝒜(ν, j) of BCGN/Fonga: fixed digit multiplicities
ν, arbitrarily many 1s, no 0s. A member n of the family is 7-smooth iff
n = 2^A·3^B·7^D, i.e.

  2^A·3^B·7^D = Σ over arrangements … (the explicit decimal expansion),

an exponential-Diophantine equation in the insertion positions. BCGN reduce
completeness of their backward graphs to equations of the shape
2^h·(10^{a₀} + 18·Σ cᵢ·10^{aᵢ}) + τ_h = 3^u·7^w; Fonga (arXiv:2608.27802,
Cor. 3.2) proves the needed uniform bound v₂(n) ≤ C(ν) over each family in
every base, making each family decidable — but the per-target computation has
not been carried out. We verify Fonga's worked example in §6.

**The final gap, precisely.** After Theorems A–E the conjecture is equivalent to:

  (★) For no (a,b,c,d) ∈ ℕ⁴ (with a·c = 0 enforced by Theorem A) does the
  sorted minimal form of Theorem C yield a chain of length ≥ 12 — equivalently,
  P(2^a·3^b·5^c·7^d) ≤ 10 for all (a,b,c,d).

and the obstruction to proving (★) is digit statistics of smooth numbers: the
Senge–Straus theorem (1973, *ineffective* — via Ridout; effective bounds are
Stewart's) proves 2^n has *unboundedly many nonzero* digits (if 2^n had ≤ C
nonzero decimal digits for infinitely many n, then 2^n would have bounded
digit sum in bases 10 and 2, contradicting Senge–Straus for the
multiplicatively independent pair (10,2)) — but a zero digit requires an
*upper*-bound statement (nonzero digits < 30% of length), which is beyond it;
heuristically P(zero-free) = 0.9^{dc} decays exponentially and the expected
number of zero-free 7-smooth numbers beyond dc = 140 is ≈ 0
(results/zero_free_results.md), but no equidistribution theorem for digits of
2^a3^b5^c7^d is known.

## Theorem F (chain closure; the exact boundary of the swept region)

Write dc_{i+1} ≤ ⌊γ·dc_i⌋ + 1 with γ = log₁₀9 = 0.95424 (from Π(m) ≤ 9^{dc(m)}
plus the +1 digit bridge). Iterating: dc(m_k) ≤ γ^k·D₀ + (1−γ^k)/(1−γ) ≈
0.6277·D₀ + 8.8 for k = 10. Let Front(k) = {7-smooth m : P(m) ≥ k, dc(m) ≤ 525}
— finite and extracted from the D=525 sweep checkpoints.

1. **No persistence-11 smooth number has dc ≤ 525** (the sweep). Hence any
   hypothetical m₀ has dc(m₀) ≥ 526.
2. Since dc decreases strictly along the chain, for any hypothetical chain
   there is a minimal i* with dc(m_{i*}) ≤ 525; i* exists whenever
   dc(m₀) ≤ 822 (because dc(m₁₀) ≤ 0.6277·dc(m₀) + 8.8 ≤ 525 ⟺ dc(m₀) ≤ 822).
3. Then m_{i*} ∈ Front(11−i*) — one of finitely many known numbers — and
   inductively every lower level is pinned to a finite set; the level above
   i*, having dc > 525, is a preimage of a known target t = m_{i*}, i.e. a
   member of a 1-insertion family 𝒜(F, j), F a digit-factorization of t,
   j = dc − |F| ≈ 500 unbounded 1s — decidable per Fonga (Theorem E) but not
   decided.
4. In particular for **dc(m₀) ≤ 549**: dc(m₁) ≤ ⌊0.95424·549⌋+1 = 525, so
   m₁ ∈ Front(10) = {4996238671872, 937638166841712}, and by Theorem D the
   digits of m₀ are one of exactly **164 multisets** — m₀ must be a 7-smooth
   member of one of 164 explicit 1-insertion families. The entire remaining
   question for 526 ≤ dc(m₀) ≤ 549 is these 164 family decisions.

So the conjecture splits cleanly: dc ≤ 525 — **closed** (sweep); 526–822 —
**reduces to finitely many explicit family decisions** (open, each decidable
per Fonga, heuristically empty: P(7-smooth) for a 95%-ones number is
astronomically small); > 822 — **open, digit-statistics territory** (§Theorem
E final paragraph). Every case is now attached to a named obstacle.

---

## §3 Certificate 1 — the thresholds τ₁,…,τ₁₀  ✅ DONE (lead)

Certified by the lead agent: results/tau_table_lead.json — the full sweep of
all 7-smooth m ≤ 4996238671872 (18,050 lattice points after exact integer
boundary filtering), table and monotonicity in Theorem B. Subagent E provides
an independent re-derivation; any disagreement is a bug in one of the two.

## §5 Certificate 2 — min-lex minimal factorizations  ✅ DONE (lead)

results/minlex_certificate.md: for all 38,880 pairs a ≤ 240, b ≤ 160 the
closed form of Theorem C.2 has (i) length == len23(a,b) (DP), (ii) no
lex-smaller minimal-length alternative (exhaustive over the bounded-count
family). Subagent E/F re-verify independently.

## §6 Certificate 3 — Fonga's machinery, verified and EXTENDED ✅ (subagent F + critic G)

Family: digits {4,4,7} plus j inserted 1s (all arrangements, no other digits).
Fonga (Thm 4.1) states max v₂ over the family = 7, attained at
111744 = 2⁷·3²·97. **Confirmed by three independent legs**
(results/fonga_verification.md, src/fonga_verify.py): (i) enumeration of all
407,253 members with j ≤ 40 — global max v₂ = 7, attained exactly once at
j = 3; (ii) Fonga's own 𝔙-recursion run verbatim — max over the *entire
infinite family* = 7, reproducing the paper's partial-sum tables
digit-for-digit; (iii) a complete mod-2⁸ residue analysis (also critic G) —
v₂ ≥ 8 is unattainable for every j ≥ 0. The 2026 preprint's flagship example
is correct.

**Extension 1 ({2,6}+1s family):** sup v₂ = 6, attained uniquely at
1216 = 2⁶·19; the v₂-growth sequence is 1 → 3 → 6 → 4 → 4 → … (peak j = 2,
plateau 4 from j = 3). Note the attaining members are *not* 7-smooth
(1216 = 2⁶·19) — v₂-attainment and smoothness are independent events, as the
theory predicts. Fonga's explicit Cor-3.2 bound (58) is valid but 10× loose.

**Extension 2 (the record family — the decisive one):** for
ν = {2, 7⁶, 8⁶, 9²} (digits of every preimage of m₀ = 2¹⁹·3⁴·7⁶ with the
rigid multiset, plus 1s), Fonga's 𝔙 **terminated in 4.6 s**:
**sup v₂ = 64 over the entire infinite family**, attained at the 53-digit
member with j = 38 ones (verified: v₂ = 64 by direct factorization, digit
multiset correct, and the member is *not* 7-smooth — rest ≡
132575558690671271338890235624201). Consequence:

> **Corollary F′.** Any 7-smooth preimage of 4996238671872 has 2-exponent
> A ≤ 64 — the level-1 exponent is finitely bounded, reducing the record-case
> family decision to a bounded 3-dimensional search (A ≤ 64; B, D bounded by
> the digit count via ln m ≤ dc·ln 10).

**Extension 3 (the explicit equation):** for the record family the level-1
constraint is the concrete exponential-Diophantine equation
`10^L − 1 + 9·10^r + 54·Σ10^{rᵢ} + 63·Σ10^{sᵢ} + 72·Σ10^{tᵢ}
= 2^A·3^{B+2}·7^D` (src/level1_diophantine.py); sampling j = 0…6
(1.26M–6.84×10¹³ arrangements): **0 of 14,000 sampled are 7-smooth** (none
even 97-smooth) — consistent with subagent C's len ≤ 30 exhaustion.

**The precise remaining decision structure** (fonga_verification.md §5): per
terminal digit δ ∈ {2,4,6,8}, per vertex s ∈ U_δ (33/9/84/51 vertices), per
digit-factorization ν (1117/1062/6377/4774 equation families), per insertion
count t ≤ t_max: decide the eq.-19 lifting — the 𝔙 half takes seconds
(demonstrated); the lifting half has never been run by anyone. And terminal
digit δ = 0 is untreatable by the method — exactly the zero-digit gap of
Theorem 5′.

---

## What a full proof would still require (final status)

Proving (★) needs, for each of the 164 level-0 candidate multisets (Theorem D)
and each deeper-level target, the non-existence of 7-smooth arrangements —
infinite 1-insertion families, each decidable per Fonga (demonstrated: the
record family's 𝔙 runs in 4.6 s and bounds A ≤ 64) but not yet decided *en
masse* (the BCGN modular-lifting half of each decision has never been run),
*plus* control of the zero-terminal-digit case, which the method cannot touch
and which is exactly the digit-statistics obstruction (§Theorem E final
paragraph; Theorem 5′). In short: the mathematics is now reduced to (1) a
finite-but-vast bundle of explicit family decisions, each mechanically
reachable in principle (the 𝔙 half demonstrably cheap), and (2) one uniform
digit-statistics conjecture. Every intermediate object is explicit and
machine-checkable; certificates: results/tau_table_lead.json,
results/threshold_certificates.json, results/minlex_certificate.md,
results/minlex_certificates.json, results/level0_maxpi_certificate.json,
results/level_feasibility.json, results/level0_multiset_counts.json,
results/fonga_verification.md, notes/critic_G_report.md.

### Verification ledger (who checked what)

| Object | Lead | Agent E | Agent F | Critic G |
|---|---|---|---|---|
| τ₁…τ₁₀ table | ✅ | ✅ (independent, agrees) | — | ✅ (re-swept) |
| min-lex F(a,b) 38,801 pairs | ✅ | ✅ (3 methods) | — | ✅ (DFS + range) |
| dc(m₀) ≥ 17 (max-Π certificate) | ✅ | ✅ (digit-sum route, D≤14) | — | — |
| 164-multiset count | ✅ | — | — | — |
| Fonga {4,4,7} example | — | — | ✅ (3 legs) | ✅ (all-j proof) |
| Record-family sup v₂ = 64 | — | — | ✅ (𝔙 + direct check) | — |
| Front(10) = 2 members | ✅ (D=525 checkpoint) | — | — | ✅ |
| Sweeps D=525 / dc≤500 | agents A/B | — | — | ✅ (frontier match) |
