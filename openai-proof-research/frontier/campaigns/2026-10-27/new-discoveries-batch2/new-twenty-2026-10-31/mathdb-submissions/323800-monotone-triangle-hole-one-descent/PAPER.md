# A proof of Riegler's linear-in-i conjecture for the monotone-triangle polynomial

*(MathDB 323800: L. Riegler, arXiv:1207.4437, Conjecture 6, eq. (4.12); FPSAC 2013, Conjecture 5, eq. (21))*

Provenance. Claude Opus 5.5 found the proof, conducted the first review, and wrote the Lean code and original manuscript. GPT-6.2 Sol conducted the cross-model review and revised the exposition.

## Abstract

Let α(n; k_1,…,k_n) be the monotone-triangle polynomial, and let A_{n,j} be the number of n×n alternating sign matrices whose first-row 1 is in column j. Riegler conjectured in 2012 that

  α(n+1; 1, 2, …, i−1, i+1, i, i+1, …, n) = − Σ_{j=1}^{n} (j−i) A_{n,j}  for 1 ≤ i ≤ n−1.

He proved the case i = 1. He proved part of the general case by a signed enumeration of generalized monotone triangles, and listed the rest as open. We prove the conjecture for all n and i.

The proof uses Fischer's operator formula and three facts derived from it:
1. Fischer's recursion.
2. A *window principle* that certifies identities among values of α by finite antisymmetrization over a block of consecutive positions.
3. A reflection symmetry.

The key new ingredient is a four-position identity (W1). It shows that α(b_{i+1}) − α(b_i) equals a duplicate-row value, which is the ASM number A_n. The Lean 4 proof starts from Fischer's operator formula and includes the recursion, the strict-row counting theorem, and the certificates checked by the kernel with `decide +kernel`. The identification with Riegler's polynomial and the conversion to refined ASM counts are explained in §1.4. The Lean endpoints depend only on propext, Classical.choice and Quot.sound.

---

## 1. The conjecture and the source's definitions

### 1.1 Riegler's definitions and conjecture

A monotone triangle of size n is an integer array (a_{i,j})_{1≤j≤i≤n} with a_{i,j} < a_{i,j+1} and a_{i+1,j} ≤ a_{i,j} ≤ a_{i+1,j+1} wherever those inequalities are defined. Riegler defines α(n; k_1,…,k_n) as the unique polynomial, of degree n−1 in each variable, that counts these triangles at strictly increasing integer bottom rows. He cites Fischer for the operator formula and gives α(5; 2,4,5,8,9) = 16939 as an example.

An alternating sign matrix (ASM) is a square matrix with entries in {0,1,−1}, nonzero entries alternating in each row and column, and all row and column sums equal to 1. Riegler writes A_{n,j} for the number of n×n ASMs with their first-row 1 in column j. He identifies it with α(n−1; 1,…,j−1,j+1,…,n) via the ASM–monotone-triangle bijection. [Riegler, arXiv:1207.4437v1, §§1 and 4](https://arxiv.org/abs/1207.4437).

**Conjecture 6 (4.12).** For n ≥ 1 and i = 1,…,n−1,

  α(n+1; 1,…,i−1,i+1,i,i+1,…,n) = − Σ_{j=1}^{n} (j−i) A_{n,j}.

In §2 Riegler defines the summation operator used for arbitrary integer bottom rows. If S_k denotes the operator for a row k of length n, the recurrence is

  S_k A = S_{(k_1,…,k_{n−1})}(Σ_{x=k_{n−1}}^{k_n} A(·,x)) − S_{(k_1,…,k_{n−2})}(A(·,k_{n−1},k_{n−1}))   (n ≥ 3).   (2.5)

The operator for a singleton row evaluates the function of the empty row. For n = 2 it is the single sum from k_1 to k_2. The extended sum from a to b is zero at b = a−1 and is the negative of the sum from b+1 to a−1 when b ≤ a−2. This is the convention in (2.4).

The [FPSAC 2013 proceedings](https://dmtcs.episciences.org/2331) state the same identity as Conjecture 5, eq. (21). The [2014 dissertation](https://utheses.univie.ac.at/detail/31168) repeats it as Conjecture 4.6.5, eq. (4.6.7), p. 75.

[Fis06] is I. Fischer, *The number of monotone triangles with prescribed bottom row*, Adv. Appl. Math. 37 (2006). Its operator formula, as recalled in Fischer, arXiv:0903.4628, eq. (1.1), is

  α(n; k_1,…,k_n) = ∏_{1≤s<t≤n} (id − E_{k_s} + E_{k_s}E_{k_t}) ∏_{1≤i<j≤n} (k_j − k_i)/(j − i),   (OF)

where E_x p(x) = p(x+1) and the product of operators is composition.

### 1.2 The Lean definitions (file `MTBasic.lean`, `MTRowsDef.lean`)

```lean
abbrev Fn (N : ℕ) := (Fin N → ℤ) → ℚ
def tr {N : ℕ} (v : Fin N → ℤ) : Module.End ℚ (Fn N)        -- f ↦ (k ↦ f (k + v))
def E {N : ℕ} (p : Fin N) : Module.End ℚ (Fn N) := tr (Pi.single p 1)          -- E_{k_p}
def pairs (N : ℕ) : List (Fin N × Fin N) :=
  (List.finRange N ×ˢ List.finRange N).filter (fun st => st.1 < st.2)
def Pi' (N : ℕ) (k : Fin N → ℤ) : ℚ :=
  ∏ i : Fin N, ∏ j ∈ Ioi i, (((k j : ℚ) - k i) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)))
def alpha (N : ℕ) (k : Fin N → ℤ) : ℚ :=
  (((pairs N).map fun st : Fin N × Fin N => (1 - E st.1 + E st.1 * E st.2)).prod) (Pi' N) k

def bRow (n i : ℕ) : Fin (n + 1) → ℤ :=      -- (1, …, i−1, i+1, i, i+1, …, n)
  fun p => if (p : ℕ) + 1 < i then (p : ℤ) + 1 else if (p : ℕ) + 1 = i then (i : ℤ) + 1 else (p : ℤ)
def rowMinus (n j : ℕ) : Fin (n - 1) → ℤ :=   -- (1, …, j−1, j+1, …, n)
  fun p => if (p : ℕ) + 1 < j then (p : ℤ) + 1 else (p : ℤ) + 2
noncomputable def A (n j : ℕ) : ℚ := alpha (n - 1) (rowMinus n j)
```

The product in `alpha` is the composition of the operators id − E_{k_s} + E_{k_s}E_{k_t} over all pairs s < t, which is exactly (OF). Indices are 0-based in Lean and 1-based in the source. In `bRow`, 0-based position p holds the source's entry at position p+1.

### 1.3 The theorem

**Theorem (MT.riegler_conjecture6).** For all natural numbers n, i with 1 ≤ i ≤ n − 1,

  α(n+1; 1, …, i−1, i+1, i, i+1, …, n) = − Σ_{j=1}^{n} (j − i) α(n−1; 1, …, j−1, j+1, …, n),

where α is given by (OF).

```lean
theorem riegler_conjecture6 (n i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ n - 1) :
    alpha (n + 1) (bRow n i) = - ∑ j ∈ Icc 1 n, ((j : ℚ) - i) * A n j
```

We also prove the following theorem in Lean.

**Theorem (MT.alpha_eq_mtNum).** For every strictly increasing k, alpha n k is the number of monotone triangles with bottom row k.

In Lean, `mtNum` counts monotone triangles through their defining row-by-row structure. The penultimate row l of a triangle with bottom row k is exactly a strictly increasing row with k_i ≤ l_i ≤ k_{i+1}. Hence A_{n,j}, as defined in Lean, is the number of monotone triangles with bottom row (1,…,j−1,j+1,…,n) (`MT.A_eq_mtNum`). The theorem with the right-hand side written as monotone-triangle counts is `MT.riegler_conjecture6_mt`.

### 1.4 What is proved in Lean and what is cited

Proved in Lean:
- everything from (OF) on;
- the recursion of α at all integer rows;
- the fact that (OF) counts monotone triangles at strictly increasing rows.

Two classical links are used outside Lean:

1. **(OF) is Riegler's polynomial α.** The operator formula is [Fischer's Theorem 1](https://arxiv.org/abs/math/0501102), cited by Riegler. Lean proves that (OF) counts monotone triangles at strictly increasing integer rows (`MT.alpha_eq_mtNum`). As a polynomial, (OF) has degree at most n−1 in each variable because the Vandermonde product has that bound and the shifts preserve it. Equality on increasing integer rows determines a polynomial uniquely. In the difference of two such polynomials, fix the first n−1 increasing entries and vary the last over infinitely many larger integers. Each coefficient in the last variable then vanishes on all increasing (n−1)-tuples, so induction gives the zero polynomial. This argument identifies the Lean formula with Riegler's α also at the conjecture's descent. The polynomial identification is made here on paper.
2. **Monotone triangles with bottom row [n]∖{j} correspond to ASMs of size n with the first-row 1 in column j.** The usual bijection records the columns with cumulative sum 1 after each successive matrix row. When the last row has its 1 in column j, the penultimate row of the triangle is [n]∖{j}. Appending the forced bottom row [n] is reversible. Reversing the order of the matrix rows then transfers the last-row refinement to the first row in the same column. Riegler uses this identification in §4, and the bijection is invoked here outside Lean.

So, in Lean, A_{n,j} is literally the number of monotone triangles with bottom row [n]∖{j}. It equals the source's ASM count by link 2.

---

## 2. Notation

Functions f : ℤ^N → ℚ are acted on by shifts: (E_p f)(k) = f(k + e_p).

All shift operators commute. We work in the commutative group algebra ℚ[ℤ^N] (Lean: `AddMonoidAlgebra ℚ (Fin N → ℤ)`). Its basis element X^v acts by f ↦ f(· + v). Write X_p = X^{e_p} and

  T_{s,t} = 1 − X_s + X_s X_t,  Q_N = ∏_{s<t} T_{s,t},  F_N(k) = det_{1≤i,j≤N} binom(k_i, j−1).

By Vandermonde's determinant, F_N(k) = ∏_{i<j}(k_j − k_i)/(j − i). (Lean: `Pi'_eq_Fdet`, via `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` with the falling factorials, and the superfactorial identity.) Hence α_N = Q_N F_N, evaluated pointwise (`alpha_eq_Q2`).

Write G_N(l) = det binom(l_i, j), Δ_p = E_p − 1, and Σ^{(k)} for Riegler's summation operator (2.5) with the convention (2.4). In Lean, `ssum a b g = Σ_{x∈[a,b+1)} g x − Σ_{x∈[b+1,a)} g x`, which is (2.4).

Two transport facts are used repeatedly. Both are elementary properties of the action:
- (i) If φ(k+v) = φ(k)+L(v) with additive L, a shift X^v before φ corresponds to X^{L(v)} after φ. This gives P(g∘φ)(k) = P′g(φ(k)) when P′ is obtained from P by this substitution (`Rel` in `MTAct.lean`). This applies to the affine insertion of a block into a fixed surrounding row.
- (ii) Shifts commute with translations: (Pf)(k + w) = P(f(· + w))(k) (`act_translate`).

---

## 3. The recursion α(N+1; k) = Σ^{(k)} α(N; l) for all k ∈ ℤ^{N+1}

This is Fischer's simplified proof (arXiv:0903.4628, §5, Lemmas 1 and 2, specialized to P = Q = 1, S = {(0,0)}, f = −1), run in the direction "(OF) ⇒ recursion".

**Lemma 1 (Fischer).** Let B : ℤ^n → ℚ satisfy, for every 1 ≤ i < n and every l with l_i = l_{i+1},

  B(l) − B(l + e_{i+1}) + B(l + e_i + e_{i+1}) = 0.   (H)

Then for every k ∈ ℤ^{n+1},

  Σ^{(k_1,…,k_{n+1})} Δ_1⋯Δ_n B = Σ_{r=1}^{n+1} (−1)^{r−1} B(k_1,…,k_{r−1}, k_{r+1}+1, …, k_{n+1}+1).

*Proof.* Induction on n. For n = 0 both sides evaluate B at the empty row. For n = 1, Σ^{(k_1,k_2)}ΔB = B(k_2+1) − B(k_1) by telescoping, including under the extended sum convention (2.4).

Let n ≥ 2, put c = k_n, and write Φ(x) for the right-hand side for (k_1,…,k_n) and the function B(·, x). By (2.5) and linearity, the first part of the operator is
  Σ_{x=c}^{k_{n+1}} [Φ(x+1) − Φ(x)] = Φ(k_{n+1}+1) − Φ(c)
by telescoping and the induction hypothesis.

For the second part we need Δ_yΔ_z B at (…, c, c). Hypothesis (H) at positions n−1, n gives Δ_yΔ_z B(…,c,c) = −B(…, c+1, c). So the second part equals +Σ^{(k_1,…,k_{n−1})} Δ⋯Δ B(·, c+1, c). By the induction hypothesis (with two fewer variables) this is a signed sum Ψ.

The terms of Ψ are the first n−1 terms of Φ(c), with the same signs. The remaining term of −Φ(c) is (−1)^n B(k_1,…,k_{n−1},c), the last term of the target. The first n terms of the target are exactly Φ(k_{n+1}+1). (Lean: `lemma1`, `L1rhs_succ`.) ∎

**Lemma 2.** Let B = Q_n G_n. Then:
- (a) B satisfies (H);
- (b) Δ_1⋯Δ_n B = Q_n F_n = α_n;
- (c) Σ_r (−1)^{r−1} B(k_1,…,k_{r−1},k_{r+1}+1,…) = Q_{n+1}F_{n+1}(k) = α_{n+1}(k).

*Proof.*

(a) The left-hand side of (H) is (T_{i+1,i}Q_n G_n)(l). The operator R = T_{i+1,i}Q_n = T_{i+1,i}T_{i,i+1}∏_{other pairs}T is invariant under swapping the variables i and i+1. The pairs (c,i), (c,i+1) are swapped as a block, because i and i+1 are adjacent. G_n is antisymmetric under that swap (it is a determinant). Hence RG_n is antisymmetric, and it vanishes where l_i = l_{i+1}. (Lean: `twoPoint`, `Q2_swap_rel`, `adjHyp_B`.)

(b) The operators Δ_p commute with Q_n. By the Leibniz expansion and Pascal's rule Δ binom(x, j) = binom(x, j−1), we get Δ_1⋯Δ_n G_n = F_n. (Lean: `Dall_act`, `Dall_Gdet`.)

(c) Consider the function k ↦ G_n(k̂_r), which does not depend on k_r. On such functions X_r acts as the identity. So T_{s,r} acts as 1, T_{r,t} acts as X_t, and the factors not involving r form Q_n in the remaining variables. Hence Q_{n+1}[G_n(k̂_r)] = (Q_n G_n)(k̂_r + Σ_{t>r} e_t).

Summing with signs and expanding F_{n+1} along its first column (all ones) gives α_{n+1}. (Lean: `Q2_del`, `Fdet_laplace`.) ∎

**Theorem R (MT.alpha_rec).** For all k ∈ ℤ^{N+1}, α(N+1; k) = Σ^{(k)} α(N; l).

*Proof.* Apply Lemma 1 to B of Lemma 2, and use (b) and (c). ∎

Two evaluations of the summation operator follow by induction from (2.5) (Lean: `S_ap`, `S_apdup`):

  Σ^{(c,c+1,…,c+n)} A = Σ_{r} A((c,…,c+n) without the r-th entry),  Σ^{(c,…,c+n,c+n)} A = A(c,…,c+n).

Hence

  α(n; 1,…,n) = Σ_{j=1}^{n} α(n−1; [n]∖{j}),  α(n+1; 1,…,n,n) = α(n; 1,…,n).   (D)

Moreover, if k is strictly increasing, then Σ^{(k)}A = Σ A(l) over the strictly increasing l with k_i ≤ l_i ≤ k_{i+1}. This is Riegler's (2.1) (Lean: `S_strict`). By induction, α_OF(k) is the number of monotone triangles with bottom row k (Lean: `alpha_eq_mtNum`).

---

## 4. Symmetries

**Translation.** α(k + c·1) = α(k). This holds because F_N depends only on differences and shifts commute with translations (`alpha_translate`).

**Reflection.** α(N; −k_N, …, −k_1) = α(N; k) (`alpha_refl`). Let ρ(k)_p = −k_{N+1−p}. Then F_N ∘ ρ = F_N.

Transport along ρ sends X_s to Z_s = X^{−e_{N+1−s}}. We have
  1 − Z_s + Z_sZ_t = Z_sZ_t · T_{N+1−t, N+1−s},
because Z_s X_{N+1−s} = 1. The pair map (s,t) ↦ (N+1−t, N+1−s) is a bijection of {s<t}. The product ∏_{s<t} Z_sZ_t is the translation by −(N−1)·1, since every index lies in exactly N−1 pairs. Hence α(ρk) = α(k − (N−1)·1) = α(k).

Combining the two: α(N; c − k_N, …, c − k_1) = α(N; k) (`alpha_refl_shift`).

---

## 5. The window principle

Fix N, a block W = {s_0+1, …, s_0+w} of consecutive positions, and a context k ∈ ℤ^N. For y ∈ ℤ^w, write k⟨y⟩ for k with the positions of W replaced by y.

Split Q_N = Q_W Q_O, where Q_W is the product over the pairs inside W and Q_O the product over the other pairs. Put F = Q_O F_N.

**Lemma (window principle).**
- (i) For each adjacent transposition τ of W, F(τk) = −F(k).
- (ii) α(N; k⟨y⟩) = (Q_w g)(y), where g(y) = F(k⟨y⟩) and Q_w is the w-variable operator.

Consequently, if Σ_x c_x (Q_w h)(x) = 0 for every h : ℤ^w → ℚ that is antisymmetric under adjacent transpositions, then

  Σ_x c_x α(N; k⟨x + a·1⟩) = 0  for all N, s_0, contexts k and shifts a ∈ ℤ.

*Proof.*

(i) Conjugation by τ permutes the factors of Q_O among themselves. A pair (c, p) with c ∉ W and p ∈ W is sent to (c, τp), and the order relation is preserved because W is a block. Pairs inside W do not occur in Q_O. And F_N∘τ = −F_N. (Lean: `cond_swap`, `QO_antisym`.)

(ii) Transport along y ↦ k⟨y⟩, which sends X^v to X^{v placed in W}. (Lean: `RelW`, `relW_QW`.)

For the consequence: g is antisymmetric by (i), and so is g(· + a·1). Translation (§2(ii)) reduces the shift a to a = 0. (Lean: `window_identity`.) ∎

**Certificates.** The hypothesis Σ_x c_x (Q_w h)(x) = 0 for all antisymmetric h is a finite check:
1. Expand Σ_x c_x δ_x · ∏_{s<t}T_{s,t} into Σ_y d_y δ_y.
2. Replace each δ_y by ±δ_{sort(y)}, or by 0 if y has a repeated entry; this is the sign of the sorting permutation.
3. Check that all coefficients cancel.

In Lean this is a verified checker: `check`, proved sound in `cert_sound`. It works on rows stored as lists of naturals with offset 64, and uses natural-number keys only to speed up comparisons. The four certificates are evaluated by the kernel (`decide +kernel`).

The checker also rejects two false variants of W1, as controls:
- W1 truncated to three positions (`check_ctrl1`);
- W1 with its last entry a+2 replaced by a+3 (`check_ctrl2`).

---

## 6. The window identities

With a ∈ ℤ arbitrary and the other entries of the row arbitrary but equal on both sides:

- **W1** (4 positions): α(…, a, a+2, a+1, a+2, …) − α(…, a+1, a, a+1, a+2, …) − α(…, a, a, a+1, a+2, …) = 0.
- **W2** (3 positions): α(…, a, a, a+1, …) = α(…, a, a+1, a+1, …).
- **W3** (4 positions): α(…, a, a, a+2, a+2, …) = α(…, a, a, a+1, a+2, …).
- **W4** (2 positions, writing W(x,y) for the window entries): W(a+1,a) + W(a,a−1) − W(a,a) + W(a−1,a) + W(a,a+1) − W(a−1,a+1) = 0.

Each follows from the window principle and its certificate (Lean: `W1`, `W2`, `W3`, `W4` in `MTWin.lean`; certificates `checkW1`–`checkW4`).

For W1, the expansion of (Σ c_x δ_x) ∏_{s<t≤4} T_{s,t} has:
- 303 nonzero terms;
- 239 of them on rows with a repeated entry, where every antisymmetric h vanishes;
- the remaining 64 in 9 orbits under permutations.

The orbits, with each term written as y:coefficient·sign(sort), are:

```
mu=(0,1,2,3): (0,3,1,2):-2*+1 (1,0,2,3):+3*-1 (2,0,1,3):+1*+1 (3,0,1,2):-2*-1 (0,1,2,3):+3*+1 (0,2,1,3):+1*-1 (0,1,3,2):+1*-1 (1,0,3,2):+1*+1  sum=0
mu=(0,1,2,4): (0,4,1,2):+1*+1 (4,0,1,2):+1*-1 (0,1,2,4):-1*+1 (1,0,2,4):-1*-1  sum=0
mu=(0,1,3,4): (0,4,1,3):-1*+1 (4,0,1,3):-1*-1  sum=0
mu=(0,2,3,4): (0,3,2,4):+1*-1 (0,4,2,3):+3*+1 (0,4,3,2):+1*-1 (3,0,2,4):+1*+1 (4,0,2,3):+3*-1 (4,0,3,2):+1*+1 (0,2,3,4):-1*+1 (2,0,3,4):-1*-1  sum=0
mu=(1,2,3,4): (1,3,2,4):-5*-1 (1,4,2,3):-15*+1 (1,4,3,2):-6*-1 (2,3,1,4):-1*+1 (2,4,1,3):-9*-1 (1,3,4,2):-1*+1 (3,4,1,2):-3*+1 (1,2,3,4):+5*+1 (2,1,3,4):+5*-1 (3,1,2,4):-5*+1 (3,2,1,4):-1*-1 (2,1,4,3):+2*+1 (3,1,4,2):-1*-1 (4,1,2,3):-12*-1 (4,2,1,3):-5*+1 (4,1,3,2):-5*+1 (4,3,1,2):-1*-1 (1,2,4,3):+2*-1  sum=0
mu=(1,2,3,5): (1,3,2,5):+1*-1 (1,5,2,3):+3*+1 (2,5,1,3):+3*-1 (1,5,3,2):+1*-1 (3,5,1,2):+1*+1 (3,1,2,5):+1*+1 (1,2,3,5):-1*+1 (2,1,3,5):-1*-1  sum=0
mu=(1,2,4,5): (1,4,2,5):-1*-1 (1,5,2,4):-1*+1 (2,5,1,4):-1*-1 (4,1,2,5):-1*+1  sum=0
mu=(1,3,4,5): (1,4,3,5):+1*-1 (1,5,3,4):+1*+1 (3,5,1,4):+1*-1 (4,1,3,5):+1*+1  sum=0
mu=(2,3,4,5): (2,4,3,5):-3*-1 (3,4,2,5):-2*+1 (2,5,3,4):-5*+1 (3,5,2,4):-5*-1 (2,5,4,3):-2*-1 (3,5,4,2):-1*+1 (4,2,3,5):-3*+1 (4,3,2,5):-1*-1  sum=0
```

This table is in Fischer's convention, so the antisymmetry is a plain swap. The proof lane used the shifted convention m_p = k_p + p and obtained the same counts (303, 239, 9, 64). The Lean check does not use this table; it recomputes everything.

---

## 7. Proof of the theorem

Let b_i = (1,…,i−1,i+1,i,i+1,…,n), dup_m = (1,…,m,m,m+1,…,n) (length n+1, the value m doubled), and A_n := α(n; 1,…,n). The case n = 1 is vacuous.

**Case n = 2** (so i = 1). By Theorem R twice and the extended sums (2.4),
  α(3; 2,1,2) = Σ_{x=1}^{2} Σ_{l=2}^{1}(…) − α(2; 1,1) = 0 − 1 = −1.
Since α(1; ·) = 1, the right-hand side is −(0·1 + 1·1) = −1. (Lean: `case_n2`.)

**Case n ≥ 3.**

*Step 1 (duplicate rows).* For 1 ≤ m ≤ n−1, W2 at positions m, m+1, m+2 gives α(dup_m) = α(dup_{m+1}). By (D), α(n+1; dup_n) = α(n+1; 1,…,n,n) = A_n. So α(dup_m) = A_n for all 1 ≤ m ≤ n. (Lean: `dup_step`, `dup_top`, `dup_val`.)

*Step 2 (linearity).* For 1 ≤ i ≤ n−2, the rows b_{i+1}, b_i and dup_i agree outside positions i, …, i+3. There they read (i, i+2, i+1, i+2), (i+1, i, i+1, i+2) and (i, i, i+1, i+2). So W1 with a = i gives α(b_{i+1}) = α(b_i) + A_n. Hence α(b_i) = α(b_1) + (i−1)A_n for 1 ≤ i ≤ n−1. (Lean: `b_step`.)

*Step 3 (anchor).* Let 2 ≤ i ≤ n−1, and apply W4 at positions i, i+1 with a = i and context b_i. Writing W(x,y) for the row with (x,y) at those positions:
- W(i+1,i) = α(b_i);
- W(i,i−1) = α(c_i), where c_i = (1,…,i−1, i, i−1, i+1,…,n);
- W(i,i), W(i−1,i) and W(i,i+1) are α(dup_i), α(dup_{i−1}) and α(dup_{i+1}), all equal to A_n;
- W(i−1,i+1) = α(1,…,i−1,i−1,i+1,i+1,i+2,…,n), which by W3 (positions i−1, …, i+2, a = i−1) equals α(dup_{i−1}) = A_n.

Hence α(b_i) = −α(c_i). (Lean: `b_neg_c`.)

By reflection with c = n+1, α(c_i) = α(b_{n+1−i}) (Lean: `c_refl`). With i = 2:
  α(b_1) + A_n = −(α(b_1) + (n−2)A_n),
so α(b_1) = −(n−1)A_n/2. Therefore

  α(n+1; b_i) = (i − (n+1)/2) A_n.

*Step 4 (right-hand side).* By (D), Σ_{j=1}^{n} A_{n,j} = A_n (Lean: `sum_A`).

By reflection at size n−1 with c = n+1, A_{n,j} = A_{n,n+1−j} (Lean: `A_symm`). Hence 2Σ_j jA_{n,j} = (n+1)Σ_j A_{n,j} (Lean: `sum_jA`). So

  −Σ_j (j−i)A_{n,j} = iA_n − ((n+1)/2)A_n = α(n+1; b_i).  ∎

(Lean: `riegler_conjecture6`. The final step is a single `linear_combination`.)

---

## 8. Checks of non-vacuity (kernel evaluation)

`MTSmall.lean` defines a computable copy `alphaR` of α through Theorem R, and proves `alpha = alphaR`. It also defines a brute-force count `mtCount` that enumerates strictly increasing upper rows from [k_1, k_n] and filters the arrays by the source's interlacing inequalities. The following are checked by the kernel:

- α(4; 1,2,3,4) = 42 = mtCount[1,2,3,4], and α(3; 1,3,5) = 26 = mtCount[1,3,5];
- A_{4,j} = 7, 14, 14, 7, which equal mtCount of [2,3,4], [1,3,4], [1,2,4], [1,2,3];
- the conjecture evaluated directly for n = 3 (i = 1, 2) and n = 4 (i = 1, 2, 3), independently of the general proof, with α(5; b_i) = −63, −21, 21;
- `mtNum 4 (1,2,3,4) = mtCount [1,2,3,4]`, which cross-checks the two monotone-triangle counts.

The cross-model review independently recomputed the conjecture for every i through n = 9 using the extended-sum recursion and ordinary monotone-triangle counts. It also checked both operator and recursion values on the conjecture rows through n = 5, checked refined counts by direct ASM enumeration through n = 6, and reproduced every coefficient in the W1 table. The script and output are `verify_323800.py` and `verification.log` in the cross-model review folder.

---

## 9. Significance

Riegler proved the i = 1 case and evaluated the GMT contribution from S3. The general evaluation remained conjectural in the 2012 preprint, the FPSAC 2013 proceedings, and the 2014 dissertation.

The proof identifies the successive difference α(b_{i+1}) − α(b_i) with a duplicate-row evaluation through the four-position identity W1. The duplicate-row value is A_n, so W1 and Riegler's i = 1 case already suffice. Section 7 instead gives the anchor from reflection and W3–W4, as in Lean.

Fischer–Riegler's factorization into an antisymmetric polynomial and their Laurent-polynomial annihilation test already give the algebraic framework for proving W1. Fix the outside entries and apply their Lemma 8.1 to the restriction of α, using (4.4) for adjacent positions in the block. Their Lemma 8.2 then proves W1 from the finite cancellation in §6. The additional step here is identifying and verifying the particular four-position relation, which was found by computer-assisted exploration. [Fischer–Riegler, arXiv:1403.0535, Lemmas 8.1–8.2](https://arxiv.org/abs/1403.0535).

## 10. Prior work

- The catalogue text of Riegler's dissertation still states the evaluation as Conjecture 4.6.5 and leaves the S1 and S2 contribution open on p. 75. The same dissertation contains the antisymmetrization lemmas in §5.9, applied there to a vertically symmetric ASM problem. [Riegler's dissertation](https://utheses.univie.ac.at/detail/31168).
- Fischer–Riegler's 2015 article cites Riegler's generalized triangles and studies a conjecture about vertically symmetric ASMs. Fischer–Reibnegger resolve the Laurent-polynomial conjecture from that article. The one-descent evaluation is outside the results of both papers. [Fischer–Riegler](https://arxiv.org/abs/1403.0535), [Fischer–Reibnegger](https://arxiv.org/abs/2608.24548).
- Later work develops general operator formulas and signed models. The cross-model review found no statement or proof of the one-descent evaluation or W1 in the later work it examined. [Fischer–Konvalinka](https://arxiv.org/abs/1910.04198), [Inoue](https://arxiv.org/abs/2306.00413), [Fischer–Höngesberg](https://arxiv.org/abs/2502.09343).

## 11. Formalization summary

Lean 4.34.1 with Mathlib at revision d13f23b7, using specific imports only. The 17 modules total 2,653 lines. Their import order is:

MTBasic, MTSum, MTDet, MTAct, MTRec, MTRows, MTCert, MTCertW1, MTCertW3, MTWindow, MTSym, MTWin, MTRowsDef, MTMain, MTFischer, MTSmall, MTAxioms.

Endpoints:
- `MT.riegler_conjecture6`;
- `MT.riegler_conjecture6_mt` (the right-hand side through monotone-triangle counts);
- `MT.alpha_eq_mtNum`.

All three depend only on propext, Classical.choice and Quot.sound. There is no sorry, admit, axiom, unsafe or native_decide. The certificates use `decide +kernel`.

Every module was compiled and checked by the standalone kernel checker through the 32 GiB runner. The receipts are in the lane folder; see REPORT.md.
