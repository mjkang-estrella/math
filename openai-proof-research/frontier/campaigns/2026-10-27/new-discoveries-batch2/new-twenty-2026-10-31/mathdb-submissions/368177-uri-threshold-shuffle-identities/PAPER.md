# Threshold shuffle identities for the uri multiplicities

*A Lean 4 proof of the corrected Conjecture A.7 of Burmester and Kühn, with a counterexample to the printed empty-middle-word case.*

Claude Opus 5.5 produced the proof, the Lean code and the first review. GPT-6.2 Sol independently audited the proof and source comparison, recomputed small cases, and revised this paper.

## Abstract

Burmester and Kühn define the uri multiplicities μ_{a,α} = B₁(ℓ(α), ind_a(α)) from Bernoulli numbers. They conjecture (Conjecture A.7) that these multiplicities satisfy two families of "threshold shuffle identities" (Definition A.5), and their post-Lie structure for the uri bracket (Theorems 5.11 and 5.14) is conditional on this conjecture. We prove identity (i) for all compositions σ, ϑ and all d₁, d₂ ≥ 0, and identity (ii) for all compositions σ, τ, ϑ with τ ≠ ∅ and all d₁, d₂ ≥ 0. We also show that (ii) with τ = ∅, read literally, is false for every multiplicity with the source's normalisation B(1,1) = 1. The source's coefficient argument uses (i) in the adjacent-factor case (§2). The proof has three ingredients.

- a cut formula expressing μ as a sum over the cuts of α;
- the compatibility of shuffles with deconcatenation;
- the generating-function identity β(p)(β(p+q)−β(q))/p + β(q)(β(p+q)−β(p))/q + β(p+q) = 0 for β(x) = x/(eˣ−1).

Lean 4 with Mathlib checks both positive identities and the counterexample under the threshold convention in §2. The endpoints depend only on the axioms propext, Classical.choice and Quot.sound.

## 1. Definitions and conjecture

The definitions below follow §5.1 and Appendix A.2 of arXiv:2504.19661v1. Each item is followed by its Lean transcription (module `TsiDefs`). In Lean, letters are integers (`List ℤ`), and the endpoints assume every letter is positive (`IsComp w := ∀ x ∈ w, 0 < x`).

**Definition 5.1.** For positive a and a composition α, ind_a(α) is the least positive index j whose prefix sum reaches a. Its value is zero when α is empty or a exceeds its weight.

```lean
noncomputable def ind (a : ℤ) (α : List ℤ) : ℕ :=
  if h : α ≠ [] ∧ a ≤ α.sum then
    Nat.find (p := fun j => 1 ≤ j ∧ j ≤ α.length ∧ a ≤ (α.take j).sum) ⟨α.length, _, le_rfl, _⟩  -- proof terms elided here; full text in TsiDefs
  else 0
```

**(44).** For m,n ≥ 0 set B₁(m,n) = (1/m!) Σ_{k=0}^{n−1} C(m,k) B_k. The table in Remark 5.2 has B₁(2,2) = 0, fixing the Bernoulli number of index 1 at −1/2. This is also the convention in the source's generating function y²x eˣ/((1−y)(e^{xy}−1)) and in Mathlib's bernoulli.

```lean
noncomputable def B1 (m n : ℕ) : ℚ :=
  (1 / (m.factorial : ℚ)) * ∑ k ∈ range n, (m.choose k : ℚ) * bernoulli k
```

**Definition 5.3.** For positive a and a composition α, put μ_{a,α} = B₁(ℓ(α), ind_a(α)) if ind_a(α) is positive, and zero otherwise.

**(55).** For a coefficient array B with B(1,1) = 1, the same rule with B in place of B₁ defines μ^B.

```lean
noncomputable def muB (B : ℕ → ℕ → ℚ) (a : ℤ) (α : List ℤ) : ℚ :=
  if a ≤ 0 then 0 else if ind a α = 0 then 0 else B α.length (ind a α)
noncomputable def mu (a : ℤ) (α : List ℤ) : ℚ := muB B1 a α
```

The source defines μ only for thresholds a ∈ ℕ. In Lean, a threshold a ≤ 0 gives 0 (see §2, reading 1).

**Word operations.** Extend μ linearly in its word argument. Concatenation joins two words in order. The shuffle counts each order-preserving interleaving, retaining repeats. Both operations extend bilinearly. Signed reversal of a word of length d reverses its letters and multiplies the result by (−1)^d.

```lean
abbrev FSum := List (ℤ × List ℤ)                     -- formal ℤ-linear sums of indices
def idx (w : List ℤ) : FSum := [(1, w)]
def shuffle : List ℤ → List ℤ → List (List ℤ)          -- recursion (19), with multiplicity
  | [], v => [v]
  | x :: u, v => shuffleCons x u (shuffle u) v          -- shuffleCons x u _ (y :: v) = x(u ⧢ yv) ++ y(xu ⧢ v)
def shuffleF (A C : FSum) : FSum := A.flatMap fun p => C.flatMap fun q => (shuffle p.2 q.2).map fun w => (p.1 * q.1, w)
def catF (A C : FSum) : FSum := A.flatMap fun p => C.map fun q => (p.1 * q.1, p.2 ++ q.2)
def revF (k : List ℤ) : FSum := [((-1) ^ k.length, k.reverse)]
noncomputable def muF (B : ℕ → ℕ → ℚ) (a : ℤ) (A : FSum) : ℚ := (A.map fun p => (p.1 : ℚ) * muB B a p.2).sum
```

**Definition A.5.** The two identities for μ^B are as follows.

(i) For all σ ∈ ℕ^{ℓ(σ)}, ϑ ∈ ℕ^{ℓ(ϑ)} and all d₁, d₂ ≥ 0,
μ^B_{t, σ⧢ϑ} = Σ_{(σ₁,σ₂)=σ, (ϑ₁,ϑ₂)=ϑ} μ^B_{|σ₂|−d₁, σ₂} μ^B_{t,(σ₁⧢ϑ₁, |σ₂|−d₁, ϑ₂)} + μ^B_{|ϑ₂|−d₂, ϑ₂} μ^B_{t,(σ₁⧢ϑ₁, |ϑ₂|−d₂, σ₂)}, where t = |σ|+|ϑ|−d₁−d₂,

(ii) For all σ ∈ ℕ^{ℓ(σ)}, τ ∈ ℕ^{ℓ(τ)}, ϑ ∈ ℕ^{ℓ(ϑ)} and all d₁, d₂ ≥ 0,
0 = Σ_{(σ₁,σ₂)=σ, (τ₁,τ₂)=τ, (ϑ₁,ϑ₂)=ϑ} μ^B_{|σ₂|+|τ₁|−d₁, σ₂⧢τ̄₁} μ^B_{t,(σ₁⧢ϑ̄₂, |σ₂|+|τ₁|−d₁, τ₂⧢ϑ̄₁)} + μ^B_{|τ₂|+|ϑ₁|−d₂, τ₂⧢ϑ̄₁} μ^B_{t,(σ₁⧢ϑ̄₂, |τ₂|+|ϑ₁|−d₂, σ₂⧢τ̄₁)}, where t = |σ|+|τ|+|ϑ|−d₁−d₂.

Decompositions allow empty parts. In Lean the decompositions (σ₁,σ₂) are (σ.take i, σ.drop i) for 0 ≤ i ≤ ℓ(σ). The inserted letter |σ₂|−d₁ is the integer `(σ.drop i).sum - d₁`:

```lean
def TSI_i (B : ℕ → ℕ → ℚ) (σ ϑ : List ℤ) (d₁ d₂ : ℕ) : Prop :=
  muF B (σ.sum + ϑ.sum - d₁ - d₂) (shuffleF (idx σ) (idx ϑ)) =
    ∑ i ∈ range (σ.length + 1), ∑ j ∈ range (ϑ.length + 1),
      (muF B ((σ.drop i).sum - d₁) (idx (σ.drop i)) *
          muF B (σ.sum + ϑ.sum - d₁ - d₂)
            (catF (catF (shuffleF (idx (σ.take i)) (idx (ϑ.take j))) (idx [(σ.drop i).sum - d₁])) (idx (ϑ.drop j))) +
        muF B ((ϑ.drop j).sum - d₂) (idx (ϑ.drop j)) *
          muF B (σ.sum + ϑ.sum - d₁ - d₂)
            (catF (catF (shuffleF (idx (σ.take i)) (idx (ϑ.take j))) (idx [(ϑ.drop j).sum - d₂])) (idx (σ.drop i))))

def TSI_ii (B : ℕ → ℕ → ℚ) (σ τ ϑ : List ℤ) (d₁ d₂ : ℕ) : Prop :=
  0 = ∑ i ∈ range (σ.length + 1), ∑ k ∈ range (τ.length + 1), ∑ j ∈ range (ϑ.length + 1),
    (muF B ((σ.drop i).sum + (τ.take k).sum - d₁) (shuffleF (idx (σ.drop i)) (revF (τ.take k))) *
        muF B (σ.sum + τ.sum + ϑ.sum - d₁ - d₂)
          (catF (catF (shuffleF (idx (σ.take i)) (revF (ϑ.drop j))) (idx [(σ.drop i).sum + (τ.take k).sum - d₁]))
            (shuffleF (idx (τ.drop k)) (revF (ϑ.take j)))) +
      muF B ((τ.drop k).sum + (ϑ.take j).sum - d₂) (shuffleF (idx (τ.drop k)) (revF (ϑ.take j))) *
        muF B (σ.sum + τ.sum + ϑ.sum - d₁ - d₂)
          (catF (catF (shuffleF (idx (σ.take i)) (revF (ϑ.drop j))) (idx [(τ.drop k).sum + (ϑ.take j).sum - d₂]))
            (shuffleF (idx (σ.drop i)) (revF (τ.take k)))))
```

**Conjecture A.7.** The conjecture asserts both identities of Definition A.5 for the uri multiplicities. The printed ranges include the empty composition.

Lean verifies both symbolic instances in Example A.6.

- (i) At (d₁,d₂,σ,ϑ) = (2,4,[1,2],[4,3]), the relation is B(4,3)+2B(4,2)+3B(4,1) = (2B(3,1)+3B(3,2)+B(3,3))B(2,1).
- (ii) At (d₁,d₂,σ,τ,ϑ) = (1,2,[2,1],[4,3],[5,6]), the relation is 0 = 6B(4,4)B(3,2)+9B(3,3)B(4,3)+21B(4,4)B(3,3)−15B(6,6).

For (ii) the computed relation has −15B(6,6)B(1,1). It equals the printed one under the source's normalisation B(1,1) = 1.

## 2. Thresholds and the empty middle word

1. **Nonpositive thresholds.** We extend μ by zero at thresholds a ≤ 0. An inserted letter c ≤ 0 makes its companion multiplicity zero, so the entire term vanishes. This implements omission of inadmissible insertions. In the derivation of Theorem 5.11, an inserted letter comes from a positive letter of a composition and the outer threshold is also positive. The convention reproduces both calculations in Example A.6.
2. **The missing hypothesis in (ii).** Set σ = τ = ∅, ϑ = (1) and d₁ = d₂ = 0. The sole nonzero product comes from the second summand with ϑ₁ = (1), giving μ^B_{1,−(1)} μ^B_{1,(1)} = −B(1,1)² = −1. The Lean endpoints tsi_ii_tau_nil_false and tsi_ii_tau_nil_false_uri give the normalized-array and uri cases. More generally, at τ = ∅, reversing and exchanging the two pieces of each cut of ϑ identifies the right side of (ii) with (−1)^ℓϑ times the right side of (i) at (σ, rev ϑ, d₁, d₂). In the proof of Theorem 5.11 the Grossman–Larson term contributes a shuffle coefficient when the marked factors are adjacent. Identity (i) equates it to the iterated-action terms. With a nonempty separating word that contribution vanishes and (ii) is the coefficient comparison. Example A.6(ii) uses a nonempty middle word. Remark A.8 expects normalized solutions, which the printed empty case excludes.

## 3. Theorem

**Theorem.** Let σ, τ, ϑ be compositions (finite sequences of positive integers, possibly empty) and d₁, d₂ ≥ 0. Then identity (i) of Definition A.5 holds for the uri multiplicities. If τ ≠ ∅, identity (ii) holds as well.

Lean (module `TsiEnd`):
```lean
theorem conjecture_A7 :
    (∀ σ ϑ : List ℤ, IsComp σ → IsComp ϑ → ∀ d₁ d₂ : ℕ, TSI_i B1 σ ϑ d₁ d₂) ∧
    (∀ σ τ ϑ : List ℤ, IsComp σ → IsComp τ → IsComp ϑ → τ ≠ [] →
      ∀ d₁ d₂ : ℕ, TSI_ii B1 σ τ ϑ d₁ d₂)
```

## 4. Proof

**Notation.**
- b_k := B_k/k!, so β(x) := x/(eˣ−1) = Σ b_k x^k, with b₀ = 1 and b₁ = −1/2.
- For words: ℓ is the length and |·| the sum of the letters.
- P(a,b) := C(a+b,a) b_{a+b}.
- [S] is the Iverson bracket.
- Σ_{w=PQ} denotes a sum over the ℓ(w)+1 decompositions of w into a prefix P and a suffix Q, empty parts allowed.

### 4.1 Lemma 1 (cut formula)
For a word α with non-negative letters, an integer d ≥ 0 and t with t + d = |α|,
  μ_{t,α} = ν_d(α) := Σ_{α=PQ} b_{ℓP} [|Q| > d] / ℓQ!.

*Proof.* Suppose t ≤ 0. Then μ = 0. Every suffix sum is at most |α| = t + d ≤ d, so every term on the right is 0.

Suppose t > 0. Then α ≠ ∅ and t ≤ |α|. Let n = ind_t(α) ∈ [1, ℓ(α)]. For 0 ≤ k ≤ ℓ(α), the suffix after k letters has sum |α| − S_k, where S_k is the k-th partial sum. We have |α| − S_k > d ⟺ S_k < t ⟺ k < n, using minimality of n and monotonicity of S_k (the letters are non-negative). So the right side is Σ_{k<n} B_k/(k!(ℓ−k)!) = B₁(ℓ, n). ∎ (Lean: `cut_formula`.)

**Applying Lemma 1 to the identities.** Every μ in (i) and (ii) has this form:
- In (i), μ_{t,σ⧢ϑ} has excess d₁+d₂ against its threshold, and μ_{|σ₂|−d₁,σ₂} has excess d₁.
- The word (w, |σ₂|−d₁, ϑ₂), with w ∈ σ₁⧢ϑ₁, has weight t + d₂.
- The same holds for (ii), with first factors over σ₂⧢τ̄₁ and τ₂⧢ϑ̄₁.

Suppose the inserted letter c is ≤ 0. Then the companion factor is μ at a threshold ≤ 0, which is 0, and the cut-form counterpart also vanishes. Otherwise all letters are nonnegative and Lemma 1 applies to both factors. Hence each summand equals its cut form with ν. (Lean: `term_i`, `term_ii`, after the literal formal sums are unfolded into shuffle sums by `muF_sh_idx`, `muF_sh_rev`, `muF_cat_i`, `muF_cat_ii`.)

### 4.2 Lemma 2 (shuffles and cuts)
For any H, Σ_{w∈u⧢v} Σ_{w=PQ} H(P,Q) = Σ_{u=u₁u₂} Σ_{v=v₁v₂} Σ_{P∈u₁⧢v₁} Σ_{Q∈u₂⧢v₂} H(P,Q).

This holds because a shuffle is a 2-colouring of positions, and a cut splits each colour class into a prefix and a suffix. In Lean (`Sh_ss`) it is proved by induction on the recursion (19).

A shuffle sum of a function that depends only on the length and weight of the shuffled word is C(ℓu+ℓv, ℓu) times its value on u v (`Sh_rep`). Hence:
- Σ_{w∈u⧢v} ν_d(w) = Σ_{u=u₁u₂, v=v₁v₂} P(ℓu₁,ℓv₁)·[|u₂|+|v₂| > d]/(ℓu₂! ℓv₂!) (`Sh_nu`);
- the same holds with v replaced by rev(v), with suffixes of rev(v) the reverses of prefixes of v (`Sh_nu_rev`).

For the second factors, ν_d(X, c, N) splits by the position of the cut:
- **(B)-cuts**: the suffix contains the inserted letter c;
- **(A)-cuts**: the suffix lies inside N.

Lemma 2 evaluates both parts (`Sh_split_i`, `Sh_split_ii`).

### 4.3 Lemma 3 (Bernoulli facts)
- (a) Σ_{r+u=N} b_u/(r+1)! = δ_{N,0} by coefficient extraction in β(x)(eˣ−1)/x = 1.
- (b) Σ_{s+t=M} C(r+s,r) C(T+t,T)/(r+T+M+1)! = 1/((r+T+1)! M!) since the numerator sum is the coefficient of z^M in (1−z)^{−r−1}(1−z)^{−T−1}.
- (c) Σ_{α+r=R, β+T=S} (−1)^β C(α+β,α) b_{α+β}/(r+T+1)! = δ_{R,0}/S!. Generating function: β(x−y)(eˣ−e^y)/(x−y) = e^y.
- (d) Σ_{r+α=R, s+β=S} (−1)^r C(α+β,α) b_{α+β}/(r+s+1)! = (−1)^R δ_{S,0}/R!. Exchange the two length variables in (c) and multiply by (−1)^R, using R = r+α.
- (e) Φ(p,q) := β(p)(β(p+q)−β(q))/p + β(q)(β(p+q)−β(p))/q + β(p+q) = 0.

  *Proof of (e).* The first difference quotient is Σ_{n,k≥0} b_{n+k+1}(p+q)^n q^k by the difference-of-powers identity. Exchanging p and q gives the second, so both are well-defined formal series. Write E_x = eˣ−1, so β(x)E_x = x. Multiplying Φ by pq E_p E_q E_{p+q} ≠ 0 in the integral domain ℚ[[p,q]] gives
  pq[(p+q)E_q − qE_{p+q} + (p+q)E_p − pE_{p+q} + (p+q)E_pE_q] = pq(p+q)[e^pe^q − e^{p+q}] = 0.

  In coefficient form, with the substitution p = x−z, q = y+z:
  H₁(A,m,B) + H₂(A,m,B) + H₃(A,m,B) = 0, where
  - H₁(A,m,B) = Σ_{i+α=A, β+γ=m, j+δ=B} (−1)^β C(α+β,α) b_{α+β} C(i+j,i) C(γ+δ,γ) b_{i+j+1+γ+δ};
  - H₂(A,m,B) = (−1)^m H₁(B,m,A);
  - H₃(A,m,B) = δ_{m,0} C(A+B,A) b_{A+B}.

  For H₁ expand the first difference quotient with n = i+j, k = γ+δ and multiply by β(x−z). Exchanging x and y and negating z gives H₂. The last term is β(x+y). The case m = 0 is F(A,B) = H₁(A,0,B) + H₁(B,0,A) + P(A,B) = 0.

Lean status of Lemma 3:
- (a), (b): `bern_a`, `bern_b`.
- (c), (d): `bern_c`, `bern_d`. In Lean these are extracted from power-series identities at numeric scalings, by a polynomial-vanishing argument.
- (e): `Phi_zero`, `H_zero`.
- Split-sum forms: `coll_a`, `coll_b`, `coll_c`, `coll_d`, `coll_F`, `coll_H1`, `coll_H2`.

**Bracket identity.** For integers X, Y and D = d₁+d₂,
  [X+Y > D] = [X > d₁][X+Y > D] + [Y > d₂][X+Y > D] − [X > d₁][Y > d₂] (`bracket`).

### 4.4 Proof of (i)
By §4.1 and Lemma 2, the left side is
  LHS = Σ_{σ=σ_aσ_b, ϑ=ϑ_aϑ_b} P(ℓσ_a,ℓϑ_a) [|σ_b|+|ϑ_b| > D] / (ℓσ_b! ℓϑ_b!).

The right side is T₁(σ,ϑ,d₁,d₂) + T₁(ϑ,σ,d₂,d₁), where
  T₁ = Σ_{σ=σ₁σ₂, ϑ=ϑ₁ϑ₂} ν_{d₁}(σ₂) Σ_{w∈σ₁⧢ϑ₁} ν_{d₂}(w, |σ₂|−d₁, ϑ₂).
The second summand is T₁ with the roles exchanged, by commutativity of ⧢.

*(B)-part of T₁.* Write ν_{d₁}(σ₂) = Σ_{σ₂=UV} b_{ℓU}[|V|>d₁]/ℓV!. Lemma 2 cuts w ∈ σ₁⧢ϑ₁ into σ₁ = σ₁'σ₁'' and ϑ₁ = ϑ₁'ϑ₁''. Put σ_a=σ₁', ϑ_a=ϑ₁', σ_b=σ₁''UV and ϑ_b=ϑ₁''ϑ₂. The outer suffix has weight |σ_b|+|ϑ_b|−d₁. Its shuffle count and factorial give C(r+s,r)/(r+s+t+1)! for r=ℓσ₁'', s=ℓϑ₁'', t=ℓϑ₂.
- The sum over the split ϑ_b = ϑ₁''ϑ₂ is evaluated by (b) (`thetaB`).
- The sum over σ_b = σ₁''·U·V with V fixed collapses by (a) to U = σ₁'' = ∅ (`sigmaB`).

This gives
  T₁^B = Σ P(ℓσ_a,ℓϑ_a) [|σ_b| > d₁][|σ_b|+|ϑ_b| > D] / (ℓσ_b! ℓϑ_b!).

*(A)-part of T₁.* The suffix W is a suffix of ϑ₂. Writing ϑ₂ = ϑ₂'W gives outer prefix length ℓσ₁+ℓϑ₁+1+ℓϑ₂'. In H₁ the lengths are i = ℓσ₁, α = ℓU, j = ℓϑ₁ and δ = ℓϑ₂', with β = γ = 0. Grouping by V, W and the prefixes σ_a = σ₁U, ϑ_a = ϑ₁ϑ₂' gives
  T₁^A = Σ_{σ=σ_aV, ϑ=ϑ_aW} [|V|>d₁][|W|>d₂]/(ℓV! ℓW!) · H₁(ℓσ_a, 0, ℓϑ_a)
(`rearr_iA`, `coll_F`). Lean: `T1_eq`.

Adding T₁(σ,ϑ,d₁,d₂) + T₁(ϑ,σ,d₂,d₁) gives
  Σ_{σ_a,σ_b,ϑ_a,ϑ_b} 1/(ℓσ_b! ℓϑ_b!) · ( P([X>d₁] + [Y>d₂])[X+Y>D] + [X>d₁][Y>d₂](H₁(A,0,B) + H₁(B,0,A)) ),
where X = |σ_b|, Y = |ϑ_b|, A = ℓσ_a, B = ℓϑ_a and P = P(A,B). Since F(A,B) = 0, we have H₁(A,0,B) + H₁(B,0,A) = −P. By the bracket identity the bracket equals P[X+Y>D], which is LHS. ∎ (Lean: `tsi_i`.)

### 4.5 Proof of (ii) for τ ≠ ∅
Put ρ = rev ϑ. A split ϑ = ϑ₁ϑ₂ corresponds to the split ρ = ρ₁ρ₂ with ρ₁ = rev ϑ₂ and ρ₂ = rev ϑ₁. By bilinearity, each summand carries the sign (−1)^{ℓτ₁+ℓϑ}. So (ii) is (−1)^{ℓϑ} times
  W = Σ_{σ=σ₁σ₂, τ=τ₁τ₂, ρ=ρ₁ρ₂} (−1)^{ℓτ₁} [ Σ_{M∈σ₂⧢rev τ₁} ν_{d₁}(M) · Σ_{X∈σ₁⧢ρ₁} Σ_{N∈τ₂⧢ρ₂} ν_{d₂}(X, c₁, N) + Σ_{N∈τ₂⧢ρ₂} ν_{d₂}(N) · Σ_{X∈σ₁⧢ρ₁} Σ_{M∈σ₂⧢rev τ₁} ν_{d₁}(X, c₂, M) ],
where X ranges over σ₁⧢ρ₁, M over σ₂⧢rev τ₁ and N over τ₂⧢ρ₂. Here c₁ = |σ₂|+|τ₁|−d₁ and c₂ = |τ₂|+|ρ₂|−d₂ (Lean: `V`, and the conversion in `tsi_ii`). We show W = 0 (Lean: `W_zero`).

*Term 1, (B)-cuts.* Split σ₁ = σ₁'σ₁'', ρ₁ = ρ₁'ρ₁'' for the outer shuffle prefix and σ₂ = UV, τ₁ = τ_p L for the inner shuffle. Put σ_a = σ₁', ρ_a = ρ₁', σ_b = σ₁''UV, ρ_b = ρ₁''ρ₂ and τ_s = Lτ₂. The inner suffix interleaves V and rev τ_p. The outer suffix has weight |σ_b|+|τ|+|ρ_b|−d₁. For r = ℓσ₁'' and T = ℓτ₂ the outer shuffle counts and denominator have the form in Lemma 3(b), with s = ℓρ₁'' and t = ℓρ₂.
- Lemma 3(b) over the split of ρ_b (`thetaB`).
- For fixed V and τ_p apply Lemma 3(c) with R = r+ℓU, S = ℓL+T and the sign (−1)^ℓL. This forces V = σ_b and supplies 1/ℓτ_s! (`sigTau`).

This gives
  W₁^B = Σ_{σ=σ_aσ_b, τ=τ_pτ_s, ρ=ρ_aρ_b} (−1)^{ℓτ_p} P(ℓσ_a,ℓρ_a)/(ℓσ_b! ℓτ_p! ℓτ_s! ℓρ_b!) · [X>d₁][X+Y>D],
with X = |σ_b|+|τ_p| and Y = |τ_s|+|ρ_b|, so that X + Y = |σ_b|+|τ|+|ρ_b| (`W1B_eq`).

*Term 2, (B)-cuts.* Split τ₂ = Lτ_s and ρ₂ = UV in the inner shuffle, and split the outer shuffle prefix as before. Put σ_b = σ₁''σ₂, ρ_b = ρ₁''UV and τ_p = τ₁ L. The inner suffix interleaves τ_s and V. The outer suffix has weight |σ_b|+|τ|+|ρ_b|−d₂.
- Lemma 3(b) over σ_b (`thetaB`).
- Lemma 3(d) sums the cuts of τ_p and ρ₁''U after Lemma 3(b) leaves the denominator (ℓρ₁''+ℓτ₁+1)! ℓσ_b!. It forces V = ρ_b and supplies (−1)^ℓτ_p/ℓτ_p! (`rhoTau`).

This gives the same sum with [Y>d₂][X+Y>D] in place of [X>d₁][X+Y>D] (`W2B_eq`).

*(A)-cuts.* Group by the suffix data (σ_b, τ_p, τ_s, ρ_b) and the middle data σ_a, τ_m, ρ_a, where τ = τ_pτ_mτ_s. Write σ₂ = Uσ_b, τ₁ = τ_p L, τ₂ = Kτ_s and ρ₂ = Vρ_b, so σ_a = σ₁U, τ_m = LK and ρ_a = ρ₁V. Their lengths split as i+α, β+γ and j+δ respectively. For term 1 the outer prefix length is i+j+1+γ+δ, its shuffle counts are C(i+j,i) and C(γ+δ,γ), and the inner prefix supplies P(α,β). Term 2 has outer prefix length i+j+1+α+β, shuffle counts C(i+j,i) and C(α+β,α), and inner prefix factor P(γ,δ). Both signs are (−1)^{ℓτ_p+β}. These are the products in H₁ and H₂ from Lemma 3(e). Each is multiplied by the same weight factor.
  (−1)^ℓτ_p [X>d₁][Y>d₂]/(ℓσ_b! ℓτ_p! ℓτ_s! ℓρ_b!).
(`W1A_eq`, `W2A_eq`). By Lemma 3(e), H₁ + H₂ = −H₃, and H₃ vanishes unless τ_m = ∅. So the (A)-parts sum to
  −Σ (−1)^ℓτ_p P [X>d₁][Y>d₂]/(ℓσ_b! ℓτ_p! ℓτ_s! ℓρ_b!)   (`WA_sum`).

*Total.* By the bracket identity,
  W = Σ_{σ_a,σ_b,ρ_a,ρ_b} P(ℓσ_a,ℓρ_a)[|σ_b|+|τ|+|ρ_b| > D]/(ℓσ_b! ℓρ_b!) · Σ_{τ=τ_pτ_s} (−1)^{ℓτ_p}/(ℓτ_p! ℓτ_s!).
The inner sum is (1−1)^{ℓτ}/ℓτ! = 0, because ℓτ ≥ 1 (`alt_zero`, `coll_alt`). This is the only place where τ ≠ ∅ is used. ∎ (Lean: `W_zero`, `tsi_ii`.)

## 5. Formal verification
- **Setup.** Lean 4.34.1 with Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. There are 23 modules, about 2,500 lines, with specific imports only. All sources are in LEAN-SOURCE-APPENDIX.md.
- **Build.** Every module was compiled and kernel-checked (`leanchecker`) through the lane's 32 GiB runner, which limits each module to 115 s CPU and 6 GiB RSS.
- **Axioms.** `#print axioms` for `conjecture_A7`, `tsi_i`, `tsi_ii`, `tsi_ii_tau_nil_false`, `tsi_ii_tau_nil_false_uri`, `example_A6_i` and `example_A6_ii` gives [propext, Classical.choice, Quot.sound].
- **Forbidden tokens.** No `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`.
- **Definitions.** The endpoints use the formal sums of §1 with the threshold convention in §2. TsiConv proves the bridge to the cut sums.
- **Examples.** Both Lean proofs of Example A.6 use the definitions in the general endpoints. The independent exact-arithmetic audit also reproduces both symbolic relations.

## 6. Consequences

The theorem supplies the coefficient identities used in Burmester–Kühn’s proof of Theorem 5.11. Their coefficient argument and post-Lie criterion give the post-Lie structure of Definition 5.5, and Theorem 5.14 then gives the dual pair of graded Hopf algebras. These consequences use the source’s argument outside Lean. The Lean endpoints cover the threshold identities and the counterexample. [Burmester–Kühn, Theorems 5.11 and 5.14](https://arxiv.org/abs/2504.19661v1)

The source’s Theorem A.3 is a binomial convolution used in Proposition 5.4 and Lemma 5.10. It handles a different coefficient comparison from the products of Bernoulli multiplicities in A.7. The authors report checking cases of A.7 computationally and point to the difficulty of the terms of mixed depth. The present proof uses standard shuffle and generating-function identities. Its main step is the grouping of cut terms, which reduces the separated-factor case to the same divided-difference identity as the adjacent-factor case. [Burmester–Kühn, §5 and Appendix A](https://arxiv.org/abs/2504.19661v1)

The homogeneity described after Definition A.5 extends the corrected identities to B_t(m,n) = t^{m−1}B₁(m,n) for t ≠ 0, as in Remark A.8(i). This is a consequence on paper.

## 7. Related results

Bachmann–Kawamura prove regularity and swap-invariant alternil closure for the bimould uri bracket. Burmester–Kühn–Schneps give the bimould uri bracket in terms of a derivation and recall the corresponding bimould post-Lie result. To deduce the threshold identities from the bimould post-Lie operation one would have to identify its action with Definition 5.5 and extract the separate coefficient comparisons. Conjecture 6.8 of Burmester–Kühn concerns the operation identification. [Bachmann–Kawamura, Theorems 6.1 and 7.1](https://arxiv.org/abs/2609.29574) · [Burmester–Kühn–Schneps, §2.4](https://arxiv.org/abs/2609.25168)

The omega registry’s resolution concerns Conjecture 4.29 of the same source, the right-factor filtration for the ari coproduct. [Issue #23147](https://github.com/the-omega-institute/trureturing/issues/23147) · [PR #23270](https://github.com/the-omega-institute/trureturing/pull/23270)
