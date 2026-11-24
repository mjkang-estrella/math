# The factor complexity of S(e,23,e)-adic languages is at most 3n

A machine-checked proof of Conjecture 53 of Garrity–Osterman (MathDB 365088).

## 1. Statement

**Source.** Thomas Garrity and Otto Vaughn Osterman, *On the Factor Complexity
Associated with a Family of Multidimensional Continued Fraction Algorithms*,
arXiv:2410.02032; *Combinatorics and Number Theory* 15:4 (2026),
DOI 10.2140/cnt.2026.15.239.

**Conjecture 53** (verbatim apart from typography):

> The complexity function p_L for S(e, 23, e)-adic language L (and any of its
> five conjugates or six twins) satisfies the bound p_L(n) ≤ 3n.

**Definition 4** (verbatim): *The factor complexity of a language L is the
function p_L that maps each positive integer n to the number of distinct words
of length n contained in L.*

**Definition 14** (verbatim): *The language associated with a coding sequence
σ = (σ₀, σ₁, σ₂, …) is the smallest possible language (by inclusion) containing
(σ₀ ∘ σ₁ ∘ ⋯ ∘ σₙ₋₁)(a) for all n ∈ ℕ and a ∈ A. Equivalently,
L(σ) = {w : w is a factor of (σ₀ ∘ σ₁ ∘ ⋯ ∘ σₙ₋₁)(c) for some n ∈ ℕ, c ∈ A}.*

For S(e,23,e) the coding sequences are sequences over the two substitutions
S0 = (1→2, 2→13, 3→3) and S1 = (1→1, 2→2, 3→13), obtained from the source's
Section 4.2 rule S_i(σ,τ0,τ1) = σ ∘ S_i(e,e,e) ∘ τ_i and printed in its
Section 10. Conjecture 53 places no condition on the coding sequence; the
source's own counterexamples for other maps (Theorem 51) use arbitrary finite
coding sequences such as 00000000000, so the intended range is all coding
sequences.

**Theorem.** For every sequence d ∈ {S0, S1}^ℕ and every n ≥ 1, the language
L(d) of Definition 14 has at most 3n distinct factors of length n. No
primitivity, recurrence, positivity or genericity hypothesis is made.

**Lean statement** (letters 1, 2, 3 are encoded as `0, 1, 2 : Fin 3`; module
`TripLanguage.lean`, unchanged from the stage-1 lane; endpoint in `TripMain.lean`):

```lean
def S0 (c : Letter) : Word := if c = 0 then [1] else if c = 1 then [0,2] else [2]
def S1 (c : Letter) : Word := if c = 0 then [0] else if c = 1 then [1] else [0,2]
def subst (b : Bool) (w : Word) : Word := w.flatMap (if b then S1 else S0)
def prefImage (d : ℕ → Bool) : ℕ → Word → Word
  | 0, w => w
  | r+1, w => prefImage d r (subst (d r) w)          -- d 0 is outermost
def lang (d : ℕ → Bool) (w : Word) : Prop :=
  ∃ (r : ℕ) (c : Letter), w <:+: prefImage d r [c]   -- Definition 14
noncomputable def complexity (L : Word → Prop) (n : ℕ) : ℕ :=
  Nat.card {w : Word // w.length = n ∧ L w}          -- Definition 4

theorem garrity_osterman_conj53 (d : ℕ → Bool) (n : ℕ) (hn : 1 ≤ n) :
    Trip.complexity (Trip.lang d) n ≤ 3 * n
```

`TripAudit.lean` also proves `S0 = ![[1],[0,2],[2]]` and `S1 = ![[0],[1],[0,2]]`
(the review's literal forms) and `lang_iff_pos_level`: reading ℕ in
Definition 14 with or without 0 gives the same language. `TripLanguage.lean`
proves that each length-n slice is a finite type (`finiteWords`), so `Nat.card`
is the genuine count; the proof also identifies it with a Finset cardinality
(`complexity_eq`).

**A degenerate example.** For the all-S1 directive the depth-r images are
1, 2 and 1^r 3, so L consists of ε, 2, 3, 1^a and 1^a 3. Its length-2 factors
are 11 and 13, hence p(1) = 3 but p(2) = 2 (`allS1_small_complexities`). This is
the literal Definition 14/Definition 4 count: Definition 14 does not require
extendability, and the letter 2 has no extension on either side. The theorem
covers such languages; the proof never assumes that L(d) is extendable.
The source does not exclude this directive (Conjecture 53 has no hypothesis on
the coding sequence, and Section 4.3 adopts Definition 14 precisely to allow
non-primitive sequences); in any case the example only illustrates that the
endpoint is stated for every directive, and the bound is trivial for it.

The parenthetical (conjugates and twins) is not formalized. The source's
Propositions 45 and 47 (proved there) identify the language of a conjugate
with a letter-permuted language, and that of a twin with a reversed language
(with S0 and S1 exchanged); both operations preserve factor complexity, so the
parenthetical follows from the theorem by the source's own results. (As
printed, Proposition 45 applies ρ where ρ⁻¹ is meant for the two 3-cycles; this
does not affect complexity.) The final check also verified directly that each
of the five conjugates and six twins listed in the source's appendix, row (4),
has substitutions π∘S_i∘π⁻¹ or π∘R(S_{1−i})∘π⁻¹ for a letter permutation π.

## 2. Proof

### 2.1 Double-Gauss blocks and the reduction

Put G_k = S1^k S0 and σ_{j,k} = G_j G_k. Then (source equation (44);
`double_gauss_letter`)

  σ_{j,k} = (1^{j+1} 3, 2^{k+1} 1^j 3, 2^k 1^j 3),  j, k ≥ 0.

Every block is a 3-free *body* followed by a single 3. Write τ = σ_{1,1}.

For a sequence g = ((j₀,k₀), (j₁,k₁), …) let L_g(i) be the factors of
σ_{g(i)} ∘ ⋯ ∘ σ_{g(i+N−1)}(c) over all N, c. Then L_g(i) is the set of factors
of σ_{g(i)}(u), u ∈ L_g(i+1) (`Lang_image`; every letter lies in some block).

*Extendability.* If g(i) = (1,1) for all large i, every L_g(i) is factorial,
contains all three letters and is two-sided extendable (`Lang_good`): a factor
of an image of a letter c at a deep level lies in an image of τ²(1) =
113113213, where every letter occurs strictly inside.

*Reduction* (`prefix_embeds`, `garrity_osterman_conj53`). Fix d and n. The
finitely many length-n factors of L(d) all occur at one level r
(`finite_factors_one_level`). Append one or two S0's to d₀ ⋯ d_{r−1} so that it
splits into an even number of Gauss blocks S1^{k} S0 (`gaussSplit`,
`pairUp`), regroup into double-Gauss blocks, and append τ forever. Since every
letter occurs in an S0-image (once or twice applied), each length-n factor of
L(d) is a factor of the new eventually-τ language at level 0. Hence it suffices
to prove p(n) ≤ 3n for eventually-τ languages L = L_g(0).

### 2.2 Unique parsing (desubstitution), proved in general

Let σ = σ_{j,k} and let L be factorial and left-extendable; let Img L be the
set of factors of σ(u), u ∈ L.

*Split lemma* (`sigma_split`). If σ(u) = A·3·R then u = u₁u₂ with σ(u₁) = A·3
and σ(u₂) = R: every 3 of σ(u) ends a block. Consequently σ is injective and
σ(u) = σ(v)·R implies u = v·u′ with σ(u′) = R.

*Exact extension edges* (`image_edge_iff`). For 3-free words x, B and any v:

  y·x·3·σ(v)·B·z ∈ Img L ⟺ ∃ c, d: c v d ∈ L, y x 3 is a suffix of 3σ(c),
  and B z is a prefix of σ(d).

(⟸ uses a left extension e of cvd: σ(e) ends with 3. ⟹ splits σ(u) at the
first 3 of x3σ(v)Bz, then peels σ(v), then reads B z inside the next block and
y x 3 inside the previous block padded by the 3 ending its predecessor.)
For 3-free w (`image_edge_free_iff`): y w z ∈ Img L ⟺ y w z is a factor of
some padded block 3σ(c).

*Unique parse* (`parse_unique`). x·3·σ(v)·B determines x (before the first 3),
B (after the last 3) and v.

*Special affixes without enumeration* (`left_affix_cases`,
`right_affix_cases`). If two different letters precede x3 in 3σ(c) and 3σ(c′),
then x3 is the longest common suffix of the two padded blocks (two
equal-length suffixes of a word coincide). One explicit witness per pair of
blocks gives x ∈ {1^j, 2^k 1^j (k>0)}. Dually, a right-special B is ε, 1^j
(k=0) or 2^k. Hence every bispecial factor containing 3 is a *child*
a·σ(v)·b with a ∈ {1^j3, 2^k1^j3}, b ∈ {ε, 1^j, 2^k} (`special_parse`), and
its extension graph is the image of E(v) under the explicit maps α, β of the
source's Proposition 71 (`child_edge_iff`, both inclusions; the maps are the
stage-1 lemmas `left_A_exact`, `left_C_exact`, `right_empty_exact`,
`right_run_exact`). Every child is longer than its antecedent, and v is
bispecial whenever the child is (`bisp_parse`). Distinct valid choices give
distinct children (`child_inj`).

### 2.3 Seeds (bispecials without 3)

Using the window form of factors of the padded blocks 3·2^p·1^q·3 with symbolic
p, q (`TripWindows`), the 3-free bispecial factors of Img L are exactly
(`seeds_sound`, `seeds_complete`):

| word | condition | type |
|---|---|---|
| ε | j,k>0 / j>0,k=0 / j=0,k>0 / j=k=0 | 221 / 205 / 244 / 484 |
| 1^j | j>0, k>0 / k=0 | 100 / 356 |
| 1^a, 1≤a<j | | 77 |
| 2^k | k>0, j>0 / j=0 | 200 / 416 |
| 2^b, 1≤b<k | j>0 / j=0 | 152 / 176 |

(A type is the 9-bit mask Σ 2^{3(a−1)+(b−1)} over edges (a,b).) Mixed words
2^b1^a are never right special, and 1^{j+1}, 2^{k+1} have one edge.

### 2.4 The 23 types

Starting from the seed types, the transform of 2.2 closes on the 23 types
11, 17, 20, 25, 26, 27, 52, 77, 80, 100, 152, 176, 200, 201, 205, 208, 216, 217,
221, 244, 356, 416, 484, with multiplicity m = |E| − |E⁻| − |E⁺| + 1 equal to +1
for 27, 216, 217, 221, −1 for 17, 20, 80, 100 and 0 otherwise. The full child
table (type, a, b) for each type and each of the four regimes (j = 0 or not,
k = 0 or not) is checked by `decide` against the transform built from the
exact maps (`childTab_check`, `child_types_check`, `states_check`). By
induction on length every bispecial factor of every level has one of these
types (`forest_typed`).

### 2.5 The matching invariant

Abstract nodes are pairs (type, Parikh vector ν ∈ ℤ³). Children of a node at a
level with parameters (j,k) have vectors M_{j,k}ν + ν(a) + ν(b), where
M_{j,k}(x,y,z) = ((j+1)x + jy + jz, (k+1)y + kz, x+y+z). The abstract forest is
F(i,0) = seeds(g i), F(i,D+1) = seeds(g i) ++ children(F(i+1,D)).

*Invariant* (`MInv`). The multiset of nodes splits into (i) pairs
(negative, positive) with δ = ν(pos) − ν(neg) ≥ 0, and δ ≥ e₃ when the negative
type is 100 or the pair is (80,27) or (20,27); (ii) at most one head (type 205,
244 or 221); (iii) at most one free positive of type 27, 216 or 217, absent if
there is no head or the head is 221, and with ν(free) − ν(head) ≥ e₃; (iv) a rest
of harmless or negative nodes.

*Preservation* (`minv_step`). Every negative and every paired positive type
has exactly one non-harmless child, of the same sign (`main_tab`); harmless and
negative types have only harmless or negative children (`inert_tab`). Pairs
propagate: in all 48 (pair type × regime) cases the new difference is
M δ plus a constant, admissible by Mδ ≥ 0 and, when δ ≥ e₃, Mδ ≥ (j,k,1)
(`adm_step`). The new seeds and the children of the head and of the free
positive are re-paired exactly as in §3b of the written proof (`hf_jk`, `hf_j0`,
`hf_0k`, `hf_00`): e.g. for j,k > 0 the new negative seed 1^j is paired with the
27-child of an old head 221 or 205 (difference Mu + e₃), or with the child of
the free positive under head 244; the head's negative child is paired with its
216-child (head 221, difference 0) or with the free positive's child (head
205, difference M(ν_f − u) + (0, κ−k, 0) ≥ 0). The new empty seed becomes the
head; at j = k = 0 the head and the free positive propagate.

*Consequence* (`minv_bound`, `forest_bound`). In each pair the negative is no
longer than the positive, so for every n, Σ_{x ∈ F, |x| < n} m(x) ≤ 1.

### 2.6 From words to the bound

The word forest (`forestW`) follows the same recursion with actual words:
seeds of level i, then children of the forest of level i+1. Mapping each word
to (type, Parikh vector) gives exactly the abstract forest (`forest_bridge`);
it is duplicate-free (`forest_nodup`); and it contains every bispecial factor of
length ≤ D at depth D, since each desubstitution shortens a word
(`forest_complete`). Hence Σ_{bispecial w, |w| < n} m(w) ≤ 1
(`bispecial_sum_le`).

For a factorial two-sided extendable language, counting words of lengths
n, n+1, n+2 through their extension sets gives
p(n+2) − 2p(n+1) + p(n) = Σ_{|w|=n} m(w) (`second_difference`), and
non-bispecial factors have m = 0 (`mult_zero_of_not_bisp`). With p(0) = 1 and
p(1) = 3 this telescopes to p(n+1) − p(n) = 2 + Σ_{|w|<n} m(w) ≤ 3
(`first_difference`). Therefore p(n) ≤ 3n for n ≥ 1 (`eventually_tau_bound`),
and by 2.1 for every directive. ∎

## 3. Verification

All 23 modules compile with Lean 4.34.1 and the pinned Mathlib
(`d13f23b723b8a846827a245b89c10fc7d3f11612`) and pass `leanchecker`. The endpoint
depends only on `propext`, `Classical.choice`, `Quot.sound`; there is no
`sorry`, `admit`, `axiom`, `unsafe` or `native_decide`. A fresh build from the
printed appendix reproduces every module with bit-identical `.olean` files
(`clean-replay/ROOT-REPLAY.json`). About 4,100 lines of Lean, of which about
3,300 are new in this stage.

## 4. Prior art (from the review, bounded searches)

The source's journal version (received 30 May 2025, revised 29 Jun 2026) still
states Conjecture 53 as open; its Section 10 sets out the bispecial program
(Props. 69–71) and ends: "To solve Conjecture 53, it remains to determine
bispecial words … characterize all nonneutral bispecial words in L, and control
their lengths." The authors' evidence is 500 random words of length 10⁴, checked
for n ≤ 500. Searches of the omega registry (issues and PRs), Principia and the
web found no proof; the nearest results are ARP (Berthé–Labbé, arXiv:1404.4189:
2n+1 ≤ p ≤ 3n+1 for a different algorithm) and the source itself. The only
citing paper located, Panti, arXiv:2506.02984, concerns topological
contractivity and gives no complexity bound. The sharpness family σ_{N,N} τ^∞ has
p(n) = 3n for n ≤ N (not formalized here; checked numerically by the final
check for N ≤ 8, where in fact p(n) = 3n for n ≤ N+1), so the bound 3n is
attained and cannot be improved, and no complexity-preserving identification
with a 2n+1 or 5n/2+1 class exists. A refresh on 2026-11-21 found nothing new: arXiv still lists v2 (21 Jul 2026)
as the latest version; OpenAlex lists two citing works (Panti, and an unrelated
survey of matrix continued fractions); the omega registry issues and pull
requests, the Principia archive, the mio-qwq and openai/math clones, GitHub code
search and the ReuF2F benchmark (cmu-l3/reuF2F, 244 problems; this conjecture
is not among them) have no entry. These are
bounded searches, not a proof of absence; probxiv.com returned HTTP 402 to the
earlier lanes and was not retried.

## 5. Significance

This settles the remaining case of the source's classification of TRIP maps
whose S-adic languages have complexity at most 3n, for every directive and with
a complete machine-checked proof from the literal definitions. The method is the
one the source advertises: Cassaigne-style bispecial counting through the
extension maps of Propositions 69–71, which the source states without proof and
which are proved here in both directions. The new mathematical ingredient, due
to the written proof this formalizes, is the length control: an injective
matching of positive to negative bispecials across different ages, governed by
nine typed Parikh cones and a free positive relative to a single neutral head.
A specialist may reasonably regard this as a careful completion of the
advertised program rather than a new technique; the result is a bounded,
elementary combinatorics statement about one two-substitution family, and it
does not by itself say anything about other TRIP families or about measure
questions such as the sibling MathDB items 365089–365090.

## 6. Attribution

Written proof by GPT-6.1 Sol; cross-model review by Claude Opus 5.5; Lean
stage 1 by GPT-6.1 Sol; final Lean stage and this paper by Claude Opus 5.5.

Written proof: `t1-pool021-proof-sol61-20261120-r1/PROOF-365088.md`. Review:
`t1-prelean-X23-opus-20261120-r1/REVIEW-365088.md`. Stage-1 modules reused
unchanged: TripLanguage, TripSanity, TripReduction, TripBlocks, ExtensionGraphs,
TripLocalMaps, TripLifting, PairCones. All other modules are new in this stage.
