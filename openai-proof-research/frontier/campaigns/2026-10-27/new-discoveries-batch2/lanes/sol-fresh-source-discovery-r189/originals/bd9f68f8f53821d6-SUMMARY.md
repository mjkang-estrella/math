# Complete binary-weight polynomial filtration component

**COMPONENT PASS.** The complete assigned filtration, coefficient-operator preservation,
quadratic Riccati induction, and odd-second-bidegree bound compile and pass a fresh
extracted strict replay. Work was solo and confined to this lane. No Jacobi
source endpoint, discovery credit, independent review, or acceptance is claimed.

## Exact representation

All declarations are in `JacobiShifted.BinaryFiltration`. The coefficient ring is
universe-polymorphic with the **sole ring assumption `[CommRing R]`**. In particular,
the arithmetic statements apply to integral coefficient rings; no rationalization,
inversion of 2, domain assumption, or coefficientwise valuation surrogate is used.

```lean
def sigma (n : ℕ) : ℕ := (Nat.digits 2 n).sum
abbrev Exponent := Fin 2 →₀ ℕ
abbrev P (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R
def weight (α : Exponent) : ℕ := sigma (α 0) + sigma (α 1) - 1
def Weighted (f : P R) : Prop :=
  f.coeff 0 = 0 ∧ ∀ α : Exponent, α ≠ 0 → (2 : R)^weight α ∣ f.coeff α

def coefficientOperator (δ : R →+ R) : P R →+ P R
def initial (A B : R) : P R :=
  MvPolynomial.monomial (Finsupp.single 0 1) A +
  MvPolynomial.monomial (Finsupp.single 1 1) B
def bidegree (i j : ℕ) : Exponent :=
  Finsupp.single 0 i + Finsupp.single 1 j
```

`initial_eq_variables` proves `initial A B = X 0 * C A + X 1 * C B`.
`bidegree_zero_coordinate` and `bidegree_one_coordinate` prove the two coordinate
formulas. `coefficientOperator` is an actual additive map built from
`AddMonoidAlgebra.map δ`; it satisfies the proved coefficient formula
`(coefficientOperator δ f).coeff α = δ (f.coeff α)`.

## Complete required interfaces

Below, `R` is arbitrary with `[CommRing R]`, `f g : P R`, and `α β : Exponent`.
The complete actual elaborated types of **all 54 named source declarations**, and
all 54 recursive axiom reports, are in `logs/12-audit.log` and independently in
`replay/fresh/logs/05-Audit.log`. `formal/Audit.lean` contains the literal
`#check` / `#print axioms` commands; `logs/declarations.json` is its inventory.

1. `BinaryDigits.lean` proves the actual binary-digit facts:

   ```lean
   sigma_zero : sigma 0 = 0
   sigma_one : sigma 1 = 1
   sigma_pos {n : ℕ} (hn : n ≠ 0) : 0 < sigma n
   sigma_double (n : ℕ) : sigma (2*n) = sigma n
   sigma_odd (n : ℕ) : sigma (2*n+1) = sigma n + 1
   sigma_odd_pred {j : ℕ} (hj : Odd j) : sigma j = sigma (j-1) + 1
   sigma_add_le (n k : ℕ) : sigma (n+k) ≤ sigma n + sigma k
   ```

   Subadditivity uses `Nat.add_choose_mul_factorial_mul_factorial`, valuation
   multiplicativity, Legendre's factorial identity, and all three explicit
   `Nat.digit_sum_le` bounds. This controls each natural subtraction. It never
   infers an inequality from a truncated Kummer subtraction.

2. `Filtration.lean` proves:

   ```lean
   sigma_coords_pos (hα : α ≠ 0) : 1 ≤ sigma (α 0) + sigma (α 1)
   weight_add_le (hα : α ≠ 0) (hβ : β ≠ 0) :
     weight (α+β) ≤ weight α + weight β + 1
   weight_double (α : Exponent) : weight (α+α) = weight α
   weighted_zero : Weighted (0 : P R)
   weighted_add (hf : Weighted f) (hg : Weighted g) : Weighted (f+g)
   weighted_neg (hf : Weighted f) : Weighted (-f)
   weighted_two_mul (hf : Weighted f) (hg : Weighted g) : Weighted (2*f*g)
   weighted_square (hf : Weighted f) : Weighted (f^2)
   ```

   `weightedSubgroup : AddSubgroup (P R)` and `weighted_sum` expose finite additive
   closure. `weighted_two_mul` expands actual polynomials using
   `MvPolynomial.as_sum` and `monomial_mul_monomial`. For `weighted_square`,
   `weighted_sum_square` inducts on the finite monomial support: inserting a
   monomial contributes its diagonal square and the paired cross term
   `2 * monomial * remainingSum`. The checked `square_add_identity` is exactly
   `(f+g)^2 = f^2 + g^2 + 2*f*g`. `weighted_monomial_square` proves diagonal
   divisibility using `weight (α+α) = weight α` and `weight α ≤ weight α + weight α`.
   There is no assumed multiplicative closure or assumed square preservation.

   `Riccati.lean` also exports the genuine polynomial coefficient convolution:

   ```lean
   coefficient_product_expansion (f g : P R) (γ : Exponent) :
     (f*g).coeff γ = ∑ α ∈ f.support, ∑ β ∈ g.support,
       if α+β = γ then f.coeff α * g.coeff β else 0
   coefficient_square_expansion (f : P R) (γ : Exponent) :
     (f^2).coeff γ = ∑ α ∈ f.support, ∑ β ∈ f.support,
       if α+β = γ then f.coeff α * f.coeff β else 0
   ```

3. The coefficient-operator preservation proof has no external preservation premise:

   ```lean
   coefficientOperator_coeff (δ : R →+ R) (f : P R) (α : Exponent) :
     (coefficientOperator δ f).coeff α = δ (f.coeff α)
   additive_nat_mul (δ : R →+ R) (m : ℕ) (x : R) :
     δ ((m : R)*x) = (m : R)*δ x
   weighted_coefficientOperator (δ : R →+ R) (hf : Weighted f) :
     Weighted (coefficientOperator δ f)
   ```

   `additive_nat_mul` is proved by `δ.map_nsmul`, and preservation rewrites the
   divisor as the cast of the natural number `2^weight α`. No derivation law is
   needed for this component. A concrete derivation can be passed by its
   underlying additive map when integrating the theorem.

4. `Riccati.lean` proves a general finite involution pairing, then specializes it
   to the full spectral convolution:

   ```lean
   weighted_involution_products {ι : Type*} (s : Finset ι) (τ : ι → ι)
     (hτ : ∀ i ∈ s, τ (τ i) = i) (hs : ∀ i ∈ s, τ i ∈ s)
     (f : ι → P R) (hf : ∀ i ∈ s, Weighted (f i)) :
     Weighted (∑ i ∈ s, f i * f (τ i))
   spectral_fixed_iff (n i : ℕ) (hi : i ≤ n) : n-i = i ↔ n = 2*i
   spectral_fixed_even_iff (n i : ℕ) (hi : i ≤ n) :
     n-i = i ↔ Even n ∧ i = n/2
   weighted_convolution (h : ℕ → P R) (n : ℕ)
     (hh : ∀ i ≤ n, Weighted (h i)) :
     Weighted (∑ i ∈ Finset.range (n+1), h i * h (n-i))
   weighted_initial (A B : R) : Weighted (initial A B)
   ```

   The involution proof is strong induction on the finite set. A fixed element
   is removed singly and contributes a square. Otherwise the distinct two-element
   orbit is removed together, and its exact sum is proved equal to `2*f i*f (τ i)`.
   For `τ i = n-i`, the proved fixed-point classification says that the only
   possible diagonal is `h (n/2)^2`, occurring precisely when `n` is even.
   `spectral_endpoints_zero` explicitly proves both endpoints vanish under `h 0=0`.
   Thus the spectral pairing and the parameter-monomial pairing are separate
   proved arguments, both used in the recurrence's proof dependency chain.

5. The general recurrence theorem has exactly these premises:

   ```lean
   theorem riccati_weighted
     (δ : R →+ R) (P₀ : P R) (h : ℕ → P R)
     (hzero : h 0 = 0) (hone : h 1 = P₀) (hP : Weighted P₀)
     (hrec : ∀ n : ℕ, 1 ≤ n →
       h (n+1) = -coefficientOperator δ (h n) -
         ∑ i ∈ Finset.range (n+1), h i * h (n-i)) :
     ∀ n : ℕ, Weighted (h n)
   ```

   `riccati_initial_weighted` specializes `P₀` to `initial A B`, discharging `hP`
   internally for arbitrary `A B : R`. The proof uses strong induction on `n`.
   `hzero`, `hone`, and `hrec` are truthful recurrence/initial-value hypotheses;
   no digit inequality, convolution closure, square closure, operator preservation,
   or unexplained polynomial model is assumed.

6. The final bound is explicit about both bidegree and total degree:

   ```lean
   odd_bidegree_weight (i j : ℕ) (hj : Odd j) :
     sigma (i+j-1) ≤ weight (bidegree i j)

   theorem riccati_degree_odd_coefficient
     (δ : R →+ R) (A B : R) (h : ℕ → P R)
     (hzero : h 0 = 0) (hone : h 1 = initial A B)
     (hrec : ∀ n : ℕ, 1 ≤ n →
       h (n+1) = -coefficientOperator δ (h n) -
         ∑ i ∈ Finset.range (n+1), h i * h (n-i))
     (n i j d : ℕ) (hj : Odd j) (hd : d = i+j) :
     (2 : R)^sigma (d-1) ∣ (h n).coeff (bidegree i j)
   ```

   `weighted_odd_coefficient` is the reusable version for any weighted polynomial;
   `riccati_odd_coefficient` omits the redundant named degree `d`.

`NonSubring.lean` proves, in `ℤ`, that `X 0` and `X 1` are weighted while their
product is not. This compiled negative control demonstrates the arithmetic
filtration's nontriviality and excludes silent use of a subring interpretation.

## Validation, commands and isolation

Pinned Lean: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`.
Actual version: `4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Pinned mathlib: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib`,
commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
No package update or library rebuild was performed.

`formal/run_lean.py` is byte-identical to the allowed template from `2ea1fd1858`.
It sets `LEAN_PATH` to the build working directory followed only by the existing
pinned package build libraries. `logs/library-pin-check.json` verifies seven
installed library/manifest files against the exact pinned mathlib Git blobs.

The final isolated replay starts from `replay/formal-source.tar.gz`, containing
only the five Lean source modules and two runners. It extracts into the previously
nonexistent `replay/fresh/source`, with **zero preexisting local `.olean` files**,
and compiles every module sequentially in dependency order. No original lane
`.olean` can satisfy a local import in that replay.

From this lane, the actual complete fresh-replay command was:

```bash
python3 replay.py
```

For a further replay, choose a new directory within this lane:

```bash
python3 replay.py replay/another-fresh
```

Each extracted module was invoked by the guard with:

```bash
python3 run_lean.py -j1 -M4096 -DwarningAsError=true -DautoImplicit=false \
  -o MODULE.olean MODULE.lean
```

Every source module also sets `warningAsError true` and `autoImplicit false`.
The sampled guard allows up to 3 GiB RSS and samples every 0.2 seconds; it does
not impose a 512 MiB virtual-address cap. All five replay builds exited 0, no
guard fired, and the maximum observed sampled RSS was **2083096 KiB**.
There were no OOM retries. No mathematical numerical diagnostics were needed.

The actual axiom audit covers all **54** named declarations. Every report uses
only `propext`, `Classical.choice`, and `Quot.sound` (one report needs none).
The fresh replay independently parsed and checked the same 54 recursive reports.
There is no `sorry`, `admit`, new axiom, `unsafe`, `native_decide`, `implemented_by`,
or `run_tac` in the final certificate sources.

Fresh receipt: `replay/fresh/receipt.json`.
Source archive SHA-256: `e6fd8e9cc0846ef9104d21ca3d1abf37920a2f91b67bc88ba054631420436d66`.
The machine-readable provenance includes source, template, audit, and artifact hashes.

Earlier failed compiler attempts are retained honestly as `logs/01`–`logs/09`:
missing `Mathlib.Tactic.Omega` precompiled module (corrected to Lean's actual Omega
module), stale/deprecated API names, natural-odd normalization, polynomial numeral
normalization, finite-sum order, and the coefficient finite-sum evaluation API.
All were corrected; the final build and fresh replay have no warnings or errors.
Initial read-only `git show` attempts used the wrong repository-relative path,
and the completed review was not present at the candidate's freeze; the successful
candidate read used the full `openai-proof-research/…` path, while the completed
review was read from its supplied working file. No candidate bytes were changed.

## Provenance and remaining scope

Ordinary proof: frozen `9cf59803fe`, `sol-jacobi-riccati-valuation-r4/PROOF.md`,
Sections 1–3; full-file SHA-256 `e086fe86d3dea5c2931793b5bf8eb63c26509805d7a2b15808f6abac2763d191`.
Completed independent ordinary review: `sol-jacobi-full-preliminary-review-r1/review.md`,
Section 3; full-file SHA-256 `b7d6f3a6d825014cc3717bc3da6e8d71e9c9e09f0011d6fa6bbca10018011cf9`.
The integrated binomial valuation at `fe7bfac255` is not imported or modified.
Only the permitted pinned runner template was read from the root formal lane;
no root live formal source or active GLM lane was inspected.

**No remaining gap in the assigned component.** Future integration must supply
the concrete coefficient ring, coefficient derivation's underlying additive map,
and the actual Jacobi sequence with its three stated recurrence premises.
The source-to-Riccati bridge, midpoint algebra construction/parity, primitives,
scaling, valuation/attainment bridge, and literal source endpoint are outside this
component. This component adds no ledger/count change, paper, publication,
discovery, or acceptance claim.

## Final Lean source hashes

- `Audit.lean`: `b23ebf558ff3db35bc1bee9fcad19f24c146010ba8d1686a8b4135a34bc20713`
- `BinaryDigits.lean`: `8e86eb5060262c34de7ca032e8f35810db93c8d690903ebc89b7272f8e9ab3b3`
- `Filtration.lean`: `500c57806650a01c9ed73ba05f79d3e072f6fce4eb2d399539622a5dbb57687a`
- `NonSubring.lean`: `bbd960e38a1836b35a7b2810c6ef44e3db7e30d60b71ac0b0f0469a03654e857`
- `Riccati.lean`: `e51b90809f1a8925116d751133a56ad4dd8b9c40f17471f27de6fb30d7e0220d`
