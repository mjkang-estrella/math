# Lean source appendix (MathDB 323800)

Modules in import order; each block is byte-identical to `src/<Module>.lean`.

### `MTBasic.lean`

```lean
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.List.ProdSigma

/-!
# Monotone-triangle polynomial via Fischer's operator formula

`alpha N k` is Fischer's operator formula
  α(N; k_1,…,k_N) = ∏_{1≤s<t≤N} (id − E_{k_s} + E_{k_s} E_{k_t}) ∏_{1≤i<j≤N} (k_j − k_i)/(j − i)
(I. Fischer, Adv. Appl. Math. 37 (2006); displayed as eq. (1.1) of arXiv:0903.4628),
where `E_{k_p}` is the shift `f ↦ (k ↦ f(k + e_p))` and the product of operators is composition.
-/

namespace MT

open Finset

/-- Functions `ℤ^N → ℚ`. -/
abbrev Fn (N : ℕ) := (Fin N → ℤ) → ℚ

/-- Translation operator `f ↦ (k ↦ f (k + v))`. -/
def tr {N : ℕ} (v : Fin N → ℤ) : Module.End ℚ (Fn N) where
  toFun f := fun k => f (k + v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma tr_apply {N : ℕ} (v : Fin N → ℤ) (f : Fn N) (k : Fin N → ℤ) :
    tr v f k = f (k + v) := rfl

/-- The shift operator `E_{k_p}`: `(E p f)(k) = f(k_1,…,k_p + 1,…,k_N)`. -/
def E {N : ℕ} (p : Fin N) : Module.End ℚ (Fn N) := tr (Pi.single p 1)

/-- The ordered index pairs `(s,t)` with `s < t`, as a list. -/
def pairs (N : ℕ) : List (Fin N × Fin N) :=
  (List.finRange N ×ˢ List.finRange N).filter (fun st => st.1 < st.2)

/-- `∏_{1≤i<j≤N} (k_j − k_i)/(j − i)`. -/
def Pi' (N : ℕ) (k : Fin N → ℤ) : ℚ :=
  ∏ i : Fin N, ∏ j ∈ Ioi i, (((k j : ℚ) - k i) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)))

/-- **Fischer's operator formula** for the monotone-triangle polynomial `α(N; k)`. -/
def alpha (N : ℕ) (k : Fin N → ℤ) : ℚ :=
  (((pairs N).map fun st : Fin N × Fin N => (1 - E st.1 + E st.1 * E st.2)).prod) (Pi' N) k

/-! ## Commutative model of the shift operators -/

/-- `trHom` as a monoid hom from `Multiplicative ℤ^N`. -/
def trHom (N : ℕ) : Multiplicative (Fin N → ℤ) →* Module.End ℚ (Fn N) where
  toFun v := tr (Multiplicative.toAdd v)
  map_one' := by
    apply LinearMap.ext; intro f; funext k; simp
  map_mul' v w := by
    apply LinearMap.ext; intro f; funext k
    simp [Module.End.mul_apply, add_assoc]

/-- Laurent polynomials in the shift operators. -/
abbrev Alg (N : ℕ) := AddMonoidAlgebra ℚ (Fin N → ℤ)

/-- Action of `Alg N` on `Fn N` by shifts. -/
noncomputable def act (N : ℕ) : Alg N →ₐ[ℚ] Module.End ℚ (Fn N) :=
  AddMonoidAlgebra.lift ℚ (Module.End ℚ (Fn N)) (Fin N → ℤ) (trHom N)

lemma act_single {N : ℕ} (v : Fin N → ℤ) (c : ℚ) (f : Fn N) (k : Fin N → ℤ) :
    act N (AddMonoidAlgebra.single v c) f k = c * f (k + v) := by
  simp [act, AddMonoidAlgebra.lift_single, trHom]

/-- The generator `X_p` (shift in coordinate `p`). -/
noncomputable def X {N : ℕ} (p : Fin N) : Alg N := AddMonoidAlgebra.single (Pi.single p 1) 1

lemma act_X {N : ℕ} (p : Fin N) : act N (X p) = E p := by
  apply LinearMap.ext; intro f; funext k
  simp [X, act_single, E]

/-- `T_{s,t} = 1 − X_s + X_s X_t`. -/
noncomputable def T {N : ℕ} (s t : Fin N) : Alg N := 1 - X s + X s * X t

lemma act_T {N : ℕ} (s t : Fin N) : act N (T s t) = 1 - E s + E s * E t := by
  simp [T, act_X]

/-- The pairs as a finset. -/
def pairsF (N : ℕ) : Finset (Fin N × Fin N) := univ.filter (fun st => st.1 < st.2)

/-- The full operator `∏_{s<t} T_{s,t}`. -/
noncomputable def Q (N : ℕ) : Alg N := ∏ st ∈ pairsF N, T st.1 st.2

lemma pairs_nodup (N : ℕ) : (pairs N).Nodup :=
  ((List.nodup_finRange N).product (List.nodup_finRange N)).filter _

lemma pairs_toFinset (N : ℕ) : (pairs N).toFinset = pairsF N := by
  ext ⟨s, t⟩; simp [pairs, pairsF, List.mem_product]

lemma alpha_eq_act (N : ℕ) (k : Fin N → ℤ) : alpha N k = act N (Q N) (Pi' N) k := by
  have h1 : ((pairs N).map fun st : Fin N × Fin N => (1 - E st.1 + E st.1 * E st.2)) =
      ((pairs N).map fun st => T st.1 st.2).map (act N) := by
    simp [List.map_map, Function.comp_def, act_T]
  have h2 : Q N = ((pairs N).map fun st => T st.1 st.2).prod := by
    rw [Q, ← pairs_toFinset, List.prod_toFinset _ (pairs_nodup N)]
  unfold alpha
  rw [h1, ← map_list_prod, ← h2]

end MT
```

### `MTSum.lean`

```lean
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Fischer's extended summation operator and his Lemma 1 (P = Q = 1, S = {(0,0)}, f = −1)

Reference: I. Fischer, arXiv:0903.4628, §2 and §5 (Lemma 1); the same operator is the
recursion (2.5) of L. Riegler, arXiv:1207.4437.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false

namespace MT

open Finset

/-- The extended simple sum `∑_{x=a}^{b} g(x)` of Riegler (2.4):
it is `∑_{a ≤ x ≤ b} g x` if `b ≥ a - 1` and `-∑_{b+1 ≤ x ≤ a-1} g x` otherwise. -/
def ssum (a b : ℤ) (g : ℤ → ℚ) : ℚ :=
  ∑ x ∈ Ico a (b + 1), g x - ∑ x ∈ Ico (b + 1) a, g x

lemma tele_Ico (h : ℤ → ℚ) (a : ℤ) :
    ∀ m : ℕ, ∑ x ∈ Ico a (a + m), (h (x + 1) - h x) = h (a + m) - h a
  | 0 => by simp
  | m + 1 => by
    have e : a + ((m + 1 : ℕ) : ℤ) = a + m + 1 := by push_cast; ring
    have hs : Ico a (a + m + 1) = insert (a + m) (Ico a (a + m)) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    rw [e, hs, sum_insert (by simp), tele_Ico h a m]; ring

lemma ssum_tele (a b : ℤ) (h : ℤ → ℚ) :
    ssum a b (fun x => h (x + 1) - h x) = h (b + 1) - h a := by
  unfold ssum
  rcases le_or_gt a (b + 1) with hab | hab
  · have h1 : Ico (b + 1) a = ∅ := Ico_eq_empty_of_le hab
    obtain ⟨m, hm⟩ : ∃ m : ℕ, b + 1 = a + m := ⟨(b + 1 - a).toNat, by omega⟩
    rw [h1, sum_empty, hm, tele_Ico]; ring
  · have h1 : Ico a (b + 1) = ∅ := Ico_eq_empty_of_le hab.le
    obtain ⟨m, hm⟩ : ∃ m : ℕ, a = b + 1 + m := ⟨(a - (b + 1)).toNat, by omega⟩
    rw [h1, sum_empty, hm, tele_Ico]; ring

lemma ssum_sub (a b : ℤ) (f g : ℤ → ℚ) :
    ssum a b (fun x => f x - g x) = ssum a b f - ssum a b g := by
  unfold ssum; rw [sum_sub_distrib, sum_sub_distrib]; ring

/-- Fischer's summation operator `∑^{(k_1,…,k_{n+1})}_{(l_1,…,l_n)} A(l)` in the form (2.5) of
Riegler (base cases `∑^{(k_1)} A = A` and `∑^{(k_1,k_2)} = ∑_{l_1=k_1}^{k_2}`). -/
def S : (n : ℕ) → (Fin (n + 1) → ℤ) → ((Fin n → ℤ) → ℚ) → ℚ
  | 0, _, A => A Fin.elim0
  | 1, k, A => ssum (k 0) (k 1) (fun l => A (fun _ => l))
  | n + 2, k, A =>
      ssum (k (Fin.last (n + 1)).castSucc) (k (Fin.last (n + 2)))
          (fun l => S (n + 1) (Fin.init k) (fun m => A (Fin.snoc m l : Fin (n + 2) → ℤ)))
        - S n (Fin.init (Fin.init k))
          (fun m => A (Fin.snoc (Fin.snoc m (k (Fin.last (n + 1)).castSucc) : Fin (n + 1) → ℤ)
              (k (Fin.last (n + 1)).castSucc) : Fin (n + 2) → ℤ))

lemma S_sub : ∀ (n : ℕ) (k : Fin (n + 1) → ℤ) (A B : (Fin n → ℤ) → ℚ),
    S n k (fun m => A m - B m) = S n k A - S n k B
  | 0, _, _, _ => rfl
  | 1, k, A, B => by simp only [S]; exact ssum_sub _ _ _ _
  | n + 2, k, A, B => by
    simp only [S]
    rw [show (fun l => S (n + 1) (Fin.init k)
          (fun m => A (Fin.snoc m l : Fin (n + 2) → ℤ) - B (Fin.snoc m l : Fin (n + 2) → ℤ))) =
        (fun l => S (n + 1) (Fin.init k) (fun m => A (Fin.snoc m l : Fin (n + 2) → ℤ)) -
          S (n + 1) (Fin.init k) (fun m => B (Fin.snoc m l : Fin (n + 2) → ℤ))) from
        funext fun l => S_sub (n + 1) _ _ _]
    rw [ssum_sub, S_sub n]; ring

lemma S_neg (n : ℕ) (k : Fin (n + 1) → ℤ) (A : (Fin n → ℤ) → ℚ) :
    S n k (fun m => - A m) = - S n k A := by
  have h := S_sub n k (fun _ => 0) A
  have h0 := S_sub n k (fun _ => 0) (fun _ => 0)
  simp only [sub_self, zero_sub] at h h0
  rw [h]
  have : S n k (fun _ => 0) = 0 := by linarith
  rw [this, zero_sub]

/-- `Δ_{l_1} ⋯ Δ_{l_n} B`, where `Δ` is the forward difference. -/
def Dall : (n : ℕ) → ((Fin n → ℤ) → ℚ) → (Fin n → ℤ) → ℚ
  | 0, B, l => B l
  | n + 1, B, l =>
      Dall n (fun m => B (Fin.snoc m (l (Fin.last n) + 1) : Fin (n + 1) → ℤ)) (Fin.init l)
        - Dall n (fun m => B (Fin.snoc m (l (Fin.last n)) : Fin (n + 1) → ℤ)) (Fin.init l)

lemma Dall_lin : ∀ (n : ℕ) (a b c : ℚ) (A B C : (Fin n → ℤ) → ℚ) (l : Fin n → ℤ),
    Dall n (fun m => a * A m + b * B m + c * C m) l
      = a * Dall n A l + b * Dall n B l + c * Dall n C l
  | 0, _, _, _, _, _, _, _ => rfl
  | n + 1, a, b, c, A, B, C, l => by
    simp only [Dall]
    rw [Dall_lin n, Dall_lin n]; ring

lemma Dall_zero (n : ℕ) (A : (Fin n → ℤ) → ℚ) (hA : ∀ m, A m = 0) (l : Fin n → ℤ) :
    Dall n A l = 0 := by
  have h := Dall_lin n 0 0 0 A A A l
  simp only [zero_mul, add_zero] at h
  rw [show A = fun m => (0 : ℚ) from funext hA]
  have h2 := Dall_lin n 0 0 0 (fun _ => (0:ℚ)) (fun _ => 0) (fun _ => 0) l
  simpa using h2

/-- Fischer's hypothesis in Lemma 1 (with `P = Q = 1`, `S = {(0,0)}`, `f = −1`):
`V_{l_i,l_{i+1}} B = 0` whenever `l_i = l_{i+1}`, where
`V_{x,y} = E_x + Δ_x Δ_y`, i.e. `(V_{x,y} B)(l) = B(l) − B(l + e_y) + B(l + e_x + e_y)`. -/
def AdjHyp (n : ℕ) (B : (Fin n → ℤ) → ℚ) : Prop :=
  ∀ (i j : Fin n), (j : ℕ) = i + 1 → ∀ l : Fin n → ℤ, l i = l j →
    B l - B (Function.update l j (l j + 1))
      + B (Function.update (Function.update l i (l i + 1)) j (l j + 1)) = 0

/-- Right-hand side of Fischer's Lemma 1:
`∑_r (−1)^{r} ∏_{t>r} E_{k_t} B(k_1,…,\hat{k_r},…,k_{n+1})`. -/
def L1rhs (n : ℕ) (k : Fin (n + 1) → ℤ) (B : (Fin n → ℤ) → ℚ) : ℚ :=
  ∑ r : Fin (n + 1), (-1 : ℚ) ^ (r : ℕ) *
    B (fun i => k (r.succAbove i) + if r ≤ i.castSucc then 1 else 0)

lemma L1rhs_succ (n : ℕ) (k : Fin (n + 2) → ℤ) (B : (Fin (n + 1) → ℤ) → ℚ) :
    L1rhs (n + 1) k B
      = L1rhs n (Fin.init k) (fun m => B (Fin.snoc m (k (Fin.last _) + 1) : Fin (n + 1) → ℤ))
        + (-1 : ℚ) ^ (n + 1) * B (Fin.init k) := by
  unfold L1rhs
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [Fin.coe_castSucc]
    congr 2
    funext i
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Fin.succAbove_of_le_castSucc _ _ (by simpa using Fin.le_last r),
        Fin.succ_last, if_pos (by simpa using Fin.le_last r)]
    | cast i =>
      rw [Fin.snoc_castSucc, Fin.castSucc_succAbove_castSucc]
      simp only [Fin.init, Fin.castSucc_le_castSucc_iff]
  · rw [Fin.val_last]
    congr 2
    funext i
    rw [Fin.succAbove_last, if_neg (not_le.mpr (Fin.castSucc_lt_last _))]
    simp [Fin.init]

lemma fin1_eq (f g : Fin 1 → ℤ) (h : f 0 = g 0) : f = g := by
  funext i; rw [Fin.fin_one_eq_zero i]; exact h

lemma AdjHyp_snoc (n : ℕ) (B : (Fin (n + 1) → ℤ) → ℚ) (hB : AdjHyp (n + 1) B) (x : ℤ) :
    AdjHyp n (fun m => B (Fin.snoc m x : Fin (n + 1) → ℤ)) := by
  intro i j hij l hl
  have := hB i.castSucc j.castSucc (by simpa using hij) (Fin.snoc l x : Fin (n + 1) → ℤ)
    (by simpa using hl)
  simpa [Fin.snoc_update] using this

/-- **Fischer's Lemma 1** (arXiv:0903.4628, §5), specialised to `P = Q = 1`, `S = {(0,0)}`,
`f = −1`: if `B` satisfies `AdjHyp`, then
`∑^{(k)} Δ_{l_1}⋯Δ_{l_n} B = ∑_r (−1)^{r} ∏_{t>r} E_{k_t} B(k̂_r)`. -/
lemma Dall_snoc (n : ℕ) (B : (Fin (n + 1) → ℤ) → ℚ) (m : Fin n → ℤ) (x : ℤ) :
    Dall (n + 1) B (Fin.snoc m x : Fin (n + 1) → ℤ)
      = Dall n (fun m' => B (Fin.snoc m' (x + 1) : Fin (n + 1) → ℤ)) m
        - Dall n (fun m' => B (Fin.snoc m' x : Fin (n + 1) → ℤ)) m := by
  simp only [Dall, Fin.init_snoc, Fin.snoc_last]

/-- **Fischer's Lemma 1** (arXiv:0903.4628, §5), specialised to `P = Q = 1`, `S = {(0,0)}`,
`f = −1`: if `B` satisfies `AdjHyp`, then
`∑^{(k)} Δ_{l_1}⋯Δ_{l_n} B = ∑_r (−1)^{r} ∏_{t>r} E_{k_t} B(k̂_r)`. -/
theorem lemma1 : ∀ (n : ℕ) (k : Fin (n + 1) → ℤ) (B : (Fin n → ℤ) → ℚ),
    AdjHyp n B → S n k (Dall n B) = L1rhs n k B
  | 0, k, B, _ => by
    simp only [S, Dall, L1rhs]
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_mul]
    congr 1; funext i; exact i.elim0
  | 1, k, B, _ => by
    have hD : ∀ l : ℤ, Dall 1 B (fun _ => l) = B (fun _ => l + 1) - B (fun _ => l) := by
      intro l
      simp only [Dall]
      congr 1
    simp only [S, hD]
    rw [ssum_tele (k 0) (k 1) (fun x => B (fun _ => x))]
    unfold L1rhs
    rw [Fin.sum_univ_two]
    have a1 : (0 : Fin 2).succAbove (0 : Fin 1) = 1 := by decide
    have a2 : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := by decide
    have a3 : ((0 : Fin 2) ≤ (0 : Fin 1).castSucc) = True := by decide
    have a4 : ((1 : Fin 2) ≤ (0 : Fin 1).castSucc) = False := by decide
    have f1 : (fun i : Fin 1 => k ((0 : Fin 2).succAbove i) + if (0 : Fin 2) ≤ i.castSucc then 1 else 0)
        = fun _ => k 1 + 1 := fin1_eq _ _ (by simp only [a1, a3, if_true])
    have f2 : (fun i : Fin 1 => k ((1 : Fin 2).succAbove i) + if (1 : Fin 2) ≤ i.castSucc then 1 else 0)
        = fun _ => k 0 := fin1_eq _ _ (by simp only [a2, a4, if_false, add_zero])
    rw [f1, f2]
    simp
    ring
  | n + 2, k, B, hB => by
    set c := k (Fin.last (n + 1)).castSucc with hc
    have hB1 : ∀ x, AdjHyp (n + 1) (fun m => B (Fin.snoc m x : Fin (n + 2) → ℤ)) :=
      fun x => AdjHyp_snoc (n + 1) B hB x
    have hB2 : ∀ x y, AdjHyp n (fun m => B (Fin.snoc (Fin.snoc m x : Fin (n + 1) → ℤ) y
        : Fin (n + 2) → ℤ)) :=
      fun x y => AdjHyp_snoc n _ (hB1 y) x
    set Φ : ℤ → ℚ := fun x => L1rhs (n + 1) (Fin.init k)
      (fun m => B (Fin.snoc m x : Fin (n + 2) → ℤ)) with hΦ
    have hfirst : ∀ l, S (n + 1) (Fin.init k)
        (fun m => Dall (n + 2) B (Fin.snoc m l : Fin (n + 2) → ℤ)) = Φ (l + 1) - Φ l := by
      intro l
      simp only [Dall_snoc]
      rw [S_sub, lemma1 (n + 1) _ _ (hB1 _), lemma1 (n + 1) _ _ (hB1 _)]
    have key : ∀ m' : Fin n → ℤ,
        B (Fin.snoc (Fin.snoc m' c : Fin (n + 1) → ℤ) c : Fin (n + 2) → ℤ)
        - B (Fin.snoc (Fin.snoc m' c : Fin (n + 1) → ℤ) (c + 1) : Fin (n + 2) → ℤ)
        + B (Fin.snoc (Fin.snoc m' (c + 1) : Fin (n + 1) → ℤ) (c + 1) : Fin (n + 2) → ℤ) = 0 := by
      intro m'
      have h := hB (Fin.last n).castSucc (Fin.last (n + 1)) (by simp)
        (Fin.snoc (Fin.snoc m' c : Fin (n + 1) → ℤ) c : Fin (n + 2) → ℤ) (by simp)
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.update_snoc_last, ← Fin.snoc_update] at h
      exact h
    have hsecond : ∀ m : Fin n → ℤ,
        Dall (n + 2) B (Fin.snoc (Fin.snoc m c : Fin (n + 1) → ℤ) c : Fin (n + 2) → ℤ)
        = - Dall n (fun m' => B (Fin.snoc (Fin.snoc m' (c + 1) : Fin (n + 1) → ℤ) c
            : Fin (n + 2) → ℤ)) m := by
      intro m
      simp only [Dall_snoc]
      have hz := Dall_zero n (fun m' =>
          1 * B (Fin.snoc (Fin.snoc m' c : Fin (n + 1) → ℤ) c : Fin (n + 2) → ℤ)
          + -1 * B (Fin.snoc (Fin.snoc m' c : Fin (n + 1) → ℤ) (c + 1) : Fin (n + 2) → ℤ)
          + 1 * B (Fin.snoc (Fin.snoc m' (c + 1) : Fin (n + 1) → ℤ) (c + 1) : Fin (n + 2) → ℤ))
        (fun m' => by have := key m'; linarith) m
      rw [Dall_lin] at hz
      linarith
    simp only [S, hfirst]
    rw [← hc]
    simp only [hsecond]
    rw [ssum_tele, S_neg, lemma1 n _ _ (hB2 _ _)]
    rw [L1rhs_succ (n + 1) k B]
    have h2 : Φ c = L1rhs n (Fin.init (Fin.init k))
        (fun m => B (Fin.snoc (Fin.snoc m (c + 1) : Fin (n + 1) → ℤ) c : Fin (n + 2) → ℤ))
        + (-1 : ℚ) ^ (n + 1) * B (Fin.init k) := by
      have h := L1rhs_succ n (Fin.init k) (fun m => B (Fin.snoc m c : Fin (n + 2) → ℤ))
      have e : (Fin.snoc (Fin.init (Fin.init k)) c : Fin (n + 2) → ℤ) = Fin.init k :=
        Fin.snoc_init_self (Fin.init k)
      rw [e] at h
      exact h
    rw [h2, pow_succ]
    ring

end MT
```

### `MTDet.lean`

```lean
import MTBasic
import MTSum
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Tactic.FieldSimp

/-!
# Binomial determinants

`Fdet n k = det (binom(k_i, j-1))` equals `∏_{i<j} (k_j-k_i)/(j-i)`, `Gdet n l = det (binom(l_i, j))`;
`Δ_1⋯Δ_n Gdet = Fdet`, `Gdet` is antisymmetric, and Laplace expansion of `Fdet (n+1)` along
its first column (all ones) gives `∑_r (-1)^r Gdet n (k̂_r)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false

namespace MT

open Finset Matrix Polynomial

/-- `binom(x, j)` for integer `x`, as a rational number. -/
noncomputable def bin (j : ℕ) (x : ℤ) : ℚ := (descPochhammer ℚ j).eval (x : ℚ) / (j.factorial : ℚ)

lemma bin_zero (x : ℤ) : bin 0 x = 1 := by simp [bin]

lemma bin_pascal (j : ℕ) (x : ℤ) : bin (j + 1) (x + 1) - bin (j + 1) x = bin j x := by
  unfold bin
  have h1 : (descPochhammer ℚ (j + 1)).eval ((x + 1 : ℤ) : ℚ)
      = ((x : ℚ) + 1) * (descPochhammer ℚ j).eval (x : ℚ) := by
    rw [descPochhammer_succ_left]; simp
  have h2 := descPochhammer_succ_eval j (x : ℚ)
  rw [h1, h2, Nat.factorial_succ]
  push_cast
  have hf : ((j.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp
  ring

/-- `F_n(k) = det_{1≤i,j≤n} binom(k_i, j-1)`. -/
noncomputable def Fdet (n : ℕ) (k : Fin n → ℤ) : ℚ := det (Matrix.of fun i j : Fin n => bin j (k i))

/-- `G_n(l) = det_{1≤i,j≤n} binom(l_i, j)`. -/
noncomputable def Gdet (n : ℕ) (l : Fin n → ℤ) : ℚ :=
  det (Matrix.of fun i j : Fin n => bin (j + 1) (l i))

lemma prod_sub_id (n : ℕ) :
    ∏ i : Fin n, ∏ j ∈ Ioi i, (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) = ∏ j : Fin n, (((j : ℕ).factorial : ℕ) : ℚ) := by
  cases n with
  | zero => simp
  | succ m =>
    have h := det_vandermonde_id_eq_superFactorial (R := ℚ) m
    rw [det_vandermonde] at h
    rw [h, Fin.prod_univ_eq_prod_range (fun j => (((j : ℕ).factorial : ℕ) : ℚ)) (m + 1),
      ← Nat.prod_range_succ_factorial]
    push_cast
    rfl

theorem Pi'_eq_Fdet (n : ℕ) (k : Fin n → ℤ) : Pi' n k = Fdet n k := by
  have hV : det (Matrix.of fun i j : Fin n => (descPochhammer ℚ j).eval (k i : ℚ))
      = ∏ i : Fin n, ∏ j ∈ Ioi i, ((k j : ℚ) - k i) := by
    rw [← det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i => (k i : ℚ))
      (fun j => descPochhammer ℚ j) (fun i => descPochhammer_natDegree _ _)
      (fun i => monic_descPochhammer _ _), det_vandermonde]
  have hF : Fdet n k = (∏ j : Fin n, ((((j : ℕ).factorial : ℕ) : ℚ))⁻¹) *
      det (Matrix.of fun i j : Fin n => (descPochhammer ℚ j).eval (k i : ℚ)) := by
    rw [← det_mul_row]
    unfold Fdet bin
    congr 1
    ext i j
    simp [div_eq_inv_mul]
  rw [hF, hV, prod_inv_distrib, ← prod_sub_id n]
  unfold Pi'
  simp only [div_eq_mul_inv, prod_mul_distrib, prod_inv_distrib]
  ring

lemma Gdet_swap (n : ℕ) (i j : Fin n) (hij : i ≠ j) (l : Fin n → ℤ) :
    Gdet n (fun r => l (Equiv.swap i j r)) = - Gdet n l := by
  unfold Gdet
  have := det_permute (Equiv.swap i j) (Matrix.of fun r c : Fin n => bin (c + 1) (l r))
  rw [Equiv.Perm.sign_swap hij] at this
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at this
  rw [← this]
  rfl

/-! ## Linearity of `Dall` -/

lemma Dall_add (n : ℕ) (A B : (Fin n → ℤ) → ℚ) (l : Fin n → ℤ) :
    Dall n (fun m => A m + B m) l = Dall n A l + Dall n B l := by
  have h := Dall_lin n 1 1 0 A B A l
  simp only [one_mul, zero_mul, add_zero] at h
  exact h

lemma Dall_smul (n : ℕ) (c : ℚ) (A : (Fin n → ℤ) → ℚ) (l : Fin n → ℤ) :
    Dall n (fun m => c * A m) l = c * Dall n A l := by
  have h := Dall_lin n c 0 0 A A A l
  simp only [zero_mul, add_zero] at h
  exact h

lemma Dall_mulc (n : ℕ) (c : ℚ) (A : (Fin n → ℤ) → ℚ) (l : Fin n → ℤ) :
    Dall n (fun m => A m * c) l = Dall n A l * c := by
  rw [show (fun m => A m * c) = fun m => c * A m from funext fun m => mul_comm _ _, Dall_smul,
    mul_comm]

lemma Dall_sum (n : ℕ) {ι : Type*} (s : Finset ι) (A : ι → (Fin n → ℤ) → ℚ) (l : Fin n → ℤ) :
    Dall n (fun m => ∑ x ∈ s, A x m) l = ∑ x ∈ s, Dall n (A x) l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact Dall_zero n _ (fun _ => rfl) l
  | insert a s ha ih =>
    simp only [sum_insert ha]
    rw [Dall_add, ih]

lemma Dall_prod : ∀ (n : ℕ) (g : Fin n → ℤ → ℚ) (l : Fin n → ℤ),
    Dall n (fun m => ∏ r, g r (m r)) l = ∏ r, (g r (l r + 1) - g r (l r))
  | 0, g, l => by simp [Dall]
  | n + 1, g, l => by
    simp only [Dall]
    have e : ∀ y : ℤ, (fun m : Fin n → ℤ => ∏ r : Fin (n + 1),
        g r ((Fin.snoc m y : Fin (n + 1) → ℤ) r))
        = fun m => (∏ r : Fin n, g r.castSucc (m r)) * g (Fin.last n) y := by
      intro y; funext m
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [e, e, Dall_mulc, Dall_mulc, Dall_prod n, Fin.prod_univ_castSucc (n := n)]
    simp only [Fin.init]
    ring

theorem Dall_Gdet (n : ℕ) (l : Fin n → ℤ) : Dall n (Gdet n) l = Fdet n l := by
  have hG : Gdet n = fun m => ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℚ) * ∏ r : Fin n, bin (σ.symm r + 1) (m r) := by
    funext m
    unfold Gdet
    rw [det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    exact Fintype.prod_equiv σ _ _ (fun i => by simp)
  rw [hG, Dall_sum]
  simp only [Dall_smul, Dall_prod, bin_pascal]
  unfold Fdet
  rw [det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact (Fintype.prod_equiv σ _ _ (fun i => by simp)).symm

theorem Fdet_laplace (n : ℕ) (k : Fin (n + 1) → ℤ) :
    Fdet (n + 1) k = ∑ r : Fin (n + 1), (-1 : ℚ) ^ (r : ℕ) * Gdet n (fun i => k (r.succAbove i)) := by
  unfold Fdet
  rw [det_succ_column_zero]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Matrix.of_apply, Fin.val_zero, bin_zero, mul_one]
  rfl

end MT
```

### `MTAct.lean`

```lean
import MTBasic
import MTSum
import Mathlib.Order.Fin.Basic

/-!
# Calculus of the shift action

* `act_translate`: shifts commute with translations;
* `Rel φ Q P`: `P` acting on `g ∘ φ` is `Q` acting on `g`, transported along an additive map `φ`;
* the double-product form `Q2` of Fischer's operator.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false

namespace MT

open Finset

lemma act_mul_apply {N : ℕ} (P P' : Alg N) (f : Fn N) (k : Fin N → ℤ) :
    act N (P * P') f k = act N P (act N P' f) k := by
  rw [map_mul]; rfl

lemma act_add_apply {N : ℕ} (P P' : Alg N) (f : Fn N) (k : Fin N → ℤ) :
    act N (P + P') f k = act N P f k + act N P' f k := by
  rw [map_add]; rfl

lemma act_zero_apply {N : ℕ} (f : Fn N) (k : Fin N → ℤ) : act N 0 f k = 0 := by
  rw [map_zero]; rfl

lemma act_one_apply {N : ℕ} (f : Fn N) (k : Fin N → ℤ) : act N 1 f k = f k := by
  rw [map_one]; rfl

lemma act_fun_add {N : ℕ} (P : Alg N) (f g : Fn N) (k : Fin N → ℤ) :
    act N P (fun m => f m + g m) k = act N P f k + act N P g k := by
  have : (fun m => f m + g m) = f + g := rfl
  rw [this, map_add]; rfl

lemma act_fun_smul {N : ℕ} (P : Alg N) (c : ℚ) (f : Fn N) (k : Fin N → ℤ) :
    act N P (fun m => c * f m) k = c * act N P f k := by
  have : (fun m => c * f m) = c • f := rfl
  rw [this, map_smul]; rfl

lemma act_fun_neg {N : ℕ} (P : Alg N) (f : Fn N) (k : Fin N → ℤ) :
    act N P (fun m => - f m) k = - act N P f k := by
  have := act_fun_smul P (-1) f k
  simpa using this

lemma act_fun_sum {N : ℕ} (P : Alg N) {ι : Type*} (s : Finset ι) (f : ι → Fn N)
    (k : Fin N → ℤ) : act N P (fun m => ∑ x ∈ s, f x m) k = ∑ x ∈ s, act N P (f x) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have := act_fun_smul P 0 (fun _ => 0) k
    simpa using this
  | insert a s ha ih =>
    simp only [sum_insert ha]
    rw [act_fun_add, ih]

lemma act_T_apply {N : ℕ} (s t : Fin N) (f : Fn N) (k : Fin N → ℤ) :
    act N (T s t) f k = f k - f (k + Pi.single s 1) + f (k + Pi.single s 1 + Pi.single t 1) := by
  rw [act_T]
  simp [E, Module.End.mul_apply, add_assoc]

/-- Shifts commute with translations. -/
lemma act_translate {N : ℕ} (P : Alg N) : ∀ (f : Fn N) (k w : Fin N → ℤ),
    act N P f (k + w) = act N P (fun m => f (m + w)) k := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => intro f k w; simp [act_zero_apply]
  | add P P' hP hP' => intro f k w; rw [act_add_apply, act_add_apply, hP, hP']
  | single v c => intro f k w; rw [act_single, act_single, add_right_comm]

/-- Transport relation along an additive map `φ : ℤ^a → ℤ^b`. -/
def Rel {a b : ℕ} (φ : (Fin a → ℤ) →+ (Fin b → ℤ)) (Q : Alg b) (P : Alg a) : Prop :=
  ∀ (g : Fn b) (k : Fin a → ℤ), act a P (fun m => g (φ m)) k = act b Q g (φ k)

namespace Rel

variable {a b : ℕ} {φ : (Fin a → ℤ) →+ (Fin b → ℤ)}

lemma single (v : Fin b → ℤ) (w : Fin a → ℤ) (c : ℚ) (h : φ w = v) :
    Rel φ (AddMonoidAlgebra.single v c) (AddMonoidAlgebra.single w c) := by
  intro g k
  rw [act_single, act_single, map_add, h]

lemma one : Rel φ 1 1 := by
  intro g k; rw [act_one_apply, act_one_apply]

lemma add {Q Q' : Alg b} {P P' : Alg a} (h : Rel φ Q P) (h' : Rel φ Q' P') :
    Rel φ (Q + Q') (P + P') := by
  intro g k; rw [act_add_apply, act_add_apply, h, h']

lemma neg {Q : Alg b} {P : Alg a} (h : Rel φ Q P) : Rel φ (-Q) (-P) := by
  intro g k
  have e1 : act a (-P) = - act a P := map_neg _ _
  have e2 : act b (-Q) = - act b Q := map_neg _ _
  rw [e1, e2]
  show - (act a P (fun m => g (φ m)) k) = - (act b Q g (φ k))
  rw [h]

lemma sub {Q Q' : Alg b} {P P' : Alg a} (h : Rel φ Q P) (h' : Rel φ Q' P') :
    Rel φ (Q - Q') (P - P') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h.add h'.neg

lemma mul {Q Q' : Alg b} {P P' : Alg a} (h : Rel φ Q P) (h' : Rel φ Q' P') :
    Rel φ (Q * Q') (P * P') := by
  intro g k
  rw [act_mul_apply, act_mul_apply]
  have : act a P' (fun m => g (φ m)) = fun m => act b Q' g (φ m) := funext (h' g)
  rw [this, h]

lemma ite {Q : Alg b} {P : Alg a} (c : Prop) [Decidable c] (h : Rel φ Q P) :
    Rel φ (if c then Q else 1) (if c then P else 1) := by
  split_ifs
  · exact h
  · exact one

lemma prod {ι : Type*} (s : Finset ι) (Q : ι → Alg b) (P : ι → Alg a)
    (h : ∀ x ∈ s, Rel φ (Q x) (P x)) : Rel φ (∏ x ∈ s, Q x) (∏ x ∈ s, P x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one : Rel φ 1 1)
  | insert x s hx ih =>
    rw [prod_insert hx, prod_insert hx]
    exact (h x (mem_insert_self x s)).mul (ih fun y hy => h y (mem_insert_of_mem hy))

end Rel

/-- Double-product form of Fischer's operator: `∏_t ∏_s [s<t] T_{s,t}`. -/
noncomputable def Q2 (N : ℕ) : Alg N := ∏ t : Fin N, ∏ s : Fin N, if s < t then T s t else 1

lemma Q_eq_Q2 (N : ℕ) : Q N = Q2 N := by
  unfold Q Q2 pairsF
  rw [prod_filter, Fintype.prod_prod_type, prod_comm]

lemma alpha_eq_Q2 (N : ℕ) (k : Fin N → ℤ) : alpha N k = act N (Q2 N) (Pi' N) k := by
  rw [alpha_eq_act, Q_eq_Q2]

end MT
```

### `MTRec.lean`

```lean
import MTDet
import MTAct

/-!
# Fischer's Lemma 2 and the recursion `α(n+1; k) = ∑^{(k)}_{(l)} α(n; l)`

This is Fischer's simplified proof of the operator formula (arXiv:0903.4628, §5, Lemma 2 with
`P = Q = 1`, `S = {(0,0)}`, `f = −1`, `m_j = j − 2`), run in the direction
"operator formula ⇒ recursion (2.5) of Riegler, arXiv:1207.4437".
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false

namespace MT

open Finset

/-! ## `Dall` commutes with shifts -/

lemma snoc_add_snoc {n : ℕ} (m : Fin n → ℤ) (y : ℤ) (v : Fin (n + 1) → ℤ) :
    (Fin.snoc m y : Fin (n + 1) → ℤ) + v = Fin.snoc (m + Fin.init v) (y + v (Fin.last n)) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [Fin.init]

lemma Dall_translate : ∀ (n : ℕ) (f : Fn n) (v l : Fin n → ℤ),
    Dall n (fun k => f (k + v)) l = Dall n f (l + v)
  | 0, f, v, l => rfl
  | n + 1, f, v, l => by
    simp only [Dall, snoc_add_snoc]
    rw [Dall_translate n (fun m => f (Fin.snoc m (l (Fin.last n) + 1 + v (Fin.last n))
      : Fin (n + 1) → ℤ)), Dall_translate n (fun m => f (Fin.snoc m (l (Fin.last n) + v (Fin.last n))
      : Fin (n + 1) → ℤ))]
    have e : (l + v) (Fin.last n) + 1 = l (Fin.last n) + 1 + v (Fin.last n) := by
      simp only [Pi.add_apply]; ring
    rw [e]
    rfl

lemma Dall_act {n : ℕ} (P : Alg n) : ∀ (f : Fn n) (l : Fin n → ℤ),
    Dall n (act n P f) l = act n P (Dall n f) l := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero =>
    intro f l
    rw [act_zero_apply]
    exact Dall_zero n _ (fun m => act_zero_apply f m) l
  | add P P' hP hP' =>
    intro f l
    rw [act_add_apply, ← hP, ← hP', ← Dall_add]
    congr 1; funext m; rw [act_add_apply]
  | single v c =>
    intro f l
    rw [act_single]
    have : act n (AddMonoidAlgebra.single v c) f = fun m => c * f (m + v) :=
      funext fun m => act_single v c f m
    rw [this, Dall_smul, Dall_translate]

/-! ## Swap symmetry (hypothesis of Lemma 1) -/

/-- Coordinate permutation `k ↦ k ∘ τ` as an additive map. -/
def permHom {n : ℕ} (τ : Equiv.Perm (Fin n)) : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun k := fun r => k (τ r)
  map_zero' := rfl
  map_add' _ _ := rfl

lemma permHom_single {n : ℕ} (τ : Equiv.Perm (Fin n)) (p : Fin n) :
    permHom τ (Pi.single p 1) = Pi.single (τ.symm p) 1 := by
  funext r
  simp only [permHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  by_cases h : τ r = p
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'; apply h; rw [h']; simp

lemma rel_perm_X {n : ℕ} (τ : Equiv.Perm (Fin n)) (p : Fin n) :
    Rel (permHom τ) (X (τ.symm p)) (X p) :=
  Rel.single _ _ _ (permHom_single τ p)

lemma rel_perm_T {n : ℕ} (τ : Equiv.Perm (Fin n)) (s t : Fin n) :
    Rel (permHom τ) (T (τ.symm s) (τ.symm t)) (T s t) :=
  (Rel.one.sub (rel_perm_X τ s)).add ((rel_perm_X τ s).mul (rel_perm_X τ t))

lemma twoPoint {n : ℕ} (f g : Fin n → Fin n → Alg n) (i j : Fin n) (hij : i ≠ j)
    (h : ∀ s t, ¬(s = i ∧ t = j) → ¬(s = j ∧ t = i) → f s t = g s t) :
    (∏ t, ∏ s, f s t) * (g i j * g j i) = (∏ t, ∏ s, g s t) * (f i j * f j i) := by
  classical
  have hp : ∀ F : Fin n → Fin n → Alg n, (∏ t, ∏ s, F s t)
      = F i j * F j i * ∏ p ∈ (univ.erase (j, i)).erase (i, j), F p.2 p.1 := by
    intro F
    rw [← Fintype.prod_prod_type (fun p : Fin n × Fin n => F p.2 p.1)]
    rw [← mul_prod_erase univ (fun p : Fin n × Fin n => F p.2 p.1) (mem_univ (j, i))]
    rw [← mul_prod_erase (univ.erase (j, i)) (fun p : Fin n × Fin n => F p.2 p.1)
      (show (i, j) ∈ univ.erase (j, i) from
        Finset.mem_erase.mpr ⟨by simp [Prod.ext_iff, hij], mem_univ _⟩)]
    dsimp only
    ring
  rw [hp f, hp g]
  have hrest : ∏ p ∈ (univ.erase (j, i)).erase (i, j), f p.2 p.1
      = ∏ p ∈ (univ.erase (j, i)).erase (i, j), g p.2 p.1 := by
    refine prod_congr rfl fun p hp => ?_
    simp only [mem_erase, ne_eq, mem_univ, and_true, Prod.ext_iff, not_and] at hp
    apply h
    · intro ⟨h1, h2⟩; exact hp.2 h2 h1
    · intro ⟨h1, h2⟩; exact hp.1 h2 h1
  rw [hrest]; ring

lemma prod_prod_perm {n : ℕ} (τ : Equiv.Perm (Fin n)) (F : Fin n → Fin n → Alg n) :
    ∏ t, ∏ s, F (τ s) (τ t) = ∏ t, ∏ s, F s t := by
  rw [Equiv.prod_comp τ (fun t => ∏ s, F (τ s) t)]
  exact prod_congr rfl fun t _ => Equiv.prod_comp τ (fun s => F s t)

lemma swap_lt_iff {n : ℕ} (i j : Fin n) (hj : (j : ℕ) = i + 1) (s t : Fin n)
    (h1 : ¬(s = i ∧ t = j)) (h2 : ¬(s = j ∧ t = i)) :
    (Equiv.swap i j s < Equiv.swap i j t ↔ s < t) := by
  simp only [Equiv.swap_apply_def]
  simp only [Fin.ext_iff, not_and] at h1 h2
  split_ifs with a b c d e f g h <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem Q2_swap_rel {n : ℕ} (i j : Fin n) (hj : (j : ℕ) = i + 1) :
    Rel (permHom (Equiv.swap i j)) (T j i * Q2 n) (T j i * Q2 n) := by
  have hij : i ≠ j := by intro h; rw [h] at hj; omega
  set τ := Equiv.swap i j with hτ
  have hsymm : τ.symm = τ := Equiv.symm_swap i j
  have h1 : Rel (permHom τ) (T i j * ∏ t, ∏ s, if s < t then T (τ s) (τ t) else 1) (T j i * Q2 n) := by
    have := (rel_perm_T τ j i).mul (Rel.prod univ _ _ fun t _ => Rel.prod univ _ _ fun s _ =>
      Rel.ite (s < t) (rel_perm_T τ s t))
    rw [hsymm] at this
    simpa [hτ, Equiv.swap_apply_left, Equiv.swap_apply_right, Q2] using this
  have h2 : (∏ t, ∏ s, if s < t then T (τ s) (τ t) else 1)
      = ∏ t, ∏ s, if τ s < τ t then T s t else (1 : Alg n) := by
    rw [← prod_prod_perm τ (fun s t => if τ s < τ t then T s t else (1 : Alg n))]
    refine prod_congr rfl fun t _ => prod_congr rfl fun s _ => ?_
    show _ = (if τ (τ s) < τ (τ t) then T (τ s) (τ t) else 1)
    rw [hτ, Equiv.swap_apply_self, Equiv.swap_apply_self]
  have h3 := twoPoint (fun s t => if τ s < τ t then T s t else (1 : Alg n))
    (fun s t => if s < t then T s t else 1) i j hij (fun s t a b => by
      show (if τ s < τ t then T s t else 1) = (if s < t then T s t else 1)
      simp only [hτ, swap_lt_iff i j hj s t a b])
  have hlt : i < j := by rw [Fin.lt_iff_val_lt_val]; omega
  simp only [hτ, Equiv.swap_apply_left, Equiv.swap_apply_right, if_pos hlt,
    if_neg (not_lt.mpr hlt.le), mul_one, one_mul] at h3
  rw [h2] at h1
  have e : T i j * ∏ t, ∏ s, (if τ s < τ t then T s t else (1 : Alg n)) = T j i * Q2 n := by
    rw [mul_comm, h3, Q2, mul_comm]
  rwa [e] at h1

lemma update_eq_add {n : ℕ} (l : Fin n → ℤ) (j : Fin n) :
    Function.update l j (l j + 1) = l + Pi.single j 1 := by
  funext r
  by_cases h : r = j
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

lemma update_eq_add' {n : ℕ} (l : Fin n → ℤ) (j : Fin n) (c : ℤ) (h : c = l j + 1) :
    Function.update l j c = l + Pi.single j 1 := by
  subst h; exact update_eq_add l j

/-- Fischer's `B(l) = ∏ V_{l_t,l_s} det binom(l_i, j)` satisfies the hypothesis of Lemma 1. -/
theorem adjHyp_B (n : ℕ) : AdjHyp n (act n (Q2 n) (Gdet n)) := by
  intro i j hj l hl
  have hij : i ≠ j := by intro h; rw [h] at hj; omega
  set B := act n (Q2 n) (Gdet n) with hB
  have e1 : Function.update l j (l j + 1) = l + Pi.single j 1 := update_eq_add l j
  have e2 : Function.update (Function.update l i (l i + 1)) j (l j + 1)
      = l + Pi.single j 1 + Pi.single i 1 := by
    rw [update_eq_add l i, update_eq_add' (l + Pi.single i 1) j (l j + 1)
      (by simp [Pi.single_eq_of_ne (Ne.symm hij)])]
    abel
  rw [e1, e2, ← act_T_apply j i B l, hB, ← act_mul_apply]
  have hrel := Q2_swap_rel i j hj (Gdet n) l
  have hfix : permHom (Equiv.swap i j) l = l := by
    funext r
    simp only [permHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hl]
    · rw [h2, hl]
    · rfl
  rw [hfix] at hrel
  have hneg : (fun m => Gdet n (permHom (Equiv.swap i j) m)) = fun m => - Gdet n m := by
    funext m; exact Gdet_swap n i j hij m
  rw [hneg, act_fun_neg] at hrel
  linarith

/-! ## Deleting a coordinate (Lemma 2, last step) -/

/-- `k ↦ (k_1,…,\hat{k_r},…,k_{n+1})` as an additive map. -/
def delHom {n : ℕ} (r : Fin (n + 1)) : (Fin (n + 1) → ℤ) →+ (Fin n → ℤ) where
  toFun k := fun i => k (r.succAbove i)
  map_zero' := rfl
  map_add' _ _ := rfl

lemma delHom_single_self {n : ℕ} (r : Fin (n + 1)) : delHom r (Pi.single r 1) = 0 := by
  funext i
  simp [delHom, Pi.single_eq_of_ne (Fin.succAbove_ne r i)]

lemma delHom_single_sa {n : ℕ} (r : Fin (n + 1)) (s : Fin n) :
    delHom r (Pi.single (r.succAbove s) 1) = Pi.single s 1 := by
  funext i
  simp only [delHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  by_cases h : i = s
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'; exact h (Fin.succAbove_right_injective h')

/-- `Y t`: the image of `X t` under deleting coordinate `r`. -/
noncomputable def Ydel {n : ℕ} (r : Fin (n + 1)) (t : Fin (n + 1)) : Alg n :=
  AddMonoidAlgebra.single (delHom r (Pi.single t 1)) 1

lemma Ydel_self {n : ℕ} (r : Fin (n + 1)) : Ydel r r = 1 := by
  rw [Ydel, delHom_single_self]; rfl

lemma Ydel_sa {n : ℕ} (r : Fin (n + 1)) (s : Fin n) : Ydel r (r.succAbove s) = X s := by
  rw [Ydel, delHom_single_sa]; rfl

lemma prod_ite_X {n : ℕ} (c : Fin n → Prop) [DecidablePred c] :
    (∏ t : Fin n, if c t then X t else (1 : Alg n))
      = AddMonoidAlgebra.single (fun i => if c i then (1 : ℤ) else 0) 1 := by
  have e : ∀ t, (if c t then X t else (1 : Alg n))
      = AddMonoidAlgebra.single (if c t then Pi.single t (1 : ℤ) else 0) 1 := by
    intro t; split_ifs <;> rfl
  simp only [e]
  rw [AddMonoidAlgebra.prod_single, prod_const_one]
  congr 1
  funext i
  rw [Finset.sum_apply]
  simp only [apply_ite (fun v : Fin n → ℤ => v i), Pi.single_apply, Pi.zero_apply]
  simp [Finset.sum_ite, Finset.filter_filter]

theorem Q2_del (n : ℕ) (r : Fin (n + 1)) (g : Fn n) (k : Fin (n + 1) → ℤ) :
    act (n + 1) (Q2 (n + 1)) (fun m => g (delHom r m)) k
      = act n (Q2 n) g (fun i => k (r.succAbove i) + if r ≤ i.castSucc then 1 else 0) := by
  have hrel : Rel (delHom r) (∏ t, ∏ s, if s < t then (1 - Ydel r s + Ydel r s * Ydel r t) else 1)
      (Q2 (n + 1)) :=
    Rel.prod univ _ _ fun t _ => Rel.prod univ _ _ fun s _ => Rel.ite (s < t)
      ((Rel.one.sub (Rel.single _ _ _ rfl)).add ((Rel.single _ _ _ rfl).mul (Rel.single _ _ _ rfl)))
  rw [hrel g k]
  have halg : (∏ t, ∏ s, if s < t then (1 - Ydel r s + Ydel r s * Ydel r t) else (1 : Alg n))
      = AddMonoidAlgebra.single (fun i => if r < r.succAbove i then (1 : ℤ) else 0) 1 * Q2 n := by
    rw [Fin.prod_univ_succAbove _ r, ← prod_ite_X, Q2, ← prod_mul_distrib]
    have hr : (∏ s, if s < r then (1 - Ydel r s + Ydel r s * Ydel r r) else (1 : Alg n)) = 1 := by
      rw [Ydel_self]; simp
    rw [hr, one_mul]
    refine prod_congr rfl fun t _ => ?_
    rw [Fin.prod_univ_succAbove _ r]
    simp only [Ydel_self, Ydel_sa, Fin.succAbove_lt_succAbove_iff]
    congr 1
    split_ifs <;> simp
  rw [halg, act_mul_apply, act_single, one_mul]
  refine congrArg (act n (Q2 n) g) (funext fun i => ?_)
  simp only [delHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.add_apply,
    Fin.lt_succAbove_iff_le_castSucc]

/-! ## The recursion -/

/-- **Recursion** (Riegler (2.2)/(2.5), Fischer [Fis06]) for the operator-formula polynomial:
`α(n+1; k) = ∑^{(k_1,…,k_{n+1})}_{(l_1,…,l_n)} α(n; l)` for all `k ∈ ℤ^{n+1}`. -/
theorem alpha_rec (n : ℕ) (k : Fin (n + 1) → ℤ) : alpha (n + 1) k = S n k (alpha n) := by
  set B := act n (Q2 n) (Gdet n) with hB
  have hD : Dall n B = alpha n := by
    funext l
    rw [hB, Dall_act, alpha_eq_Q2,
      show Dall n (Gdet n) = Pi' n from funext fun m => by rw [Dall_Gdet, Pi'_eq_Fdet]]
  rw [← hD, lemma1 n k B (adjHyp_B n), alpha_eq_Q2]
  have hP : Pi' (n + 1) = fun m => ∑ r : Fin (n + 1),
      (-1 : ℚ) ^ (r : ℕ) * Gdet n (delHom r m) := by
    funext m; rw [Pi'_eq_Fdet, Fdet_laplace]; rfl
  rw [hP, act_fun_sum]
  unfold L1rhs
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [act_fun_smul, Q2_del]

end MT
```

### `MTRows.lean`

```lean
import MTRec

/-!
# The summation operator on consecutive rows and on rows ending in a duplicate

* `S_ap`: `∑^{(c,c+1,…,c+n)} A = ∑_r A((c,…,c+n) with the r-th entry removed)`;
* `S_apdup`: `∑^{(c,…,c+n,c+n)} A = A(c,…,c+n)`.

Consequently `α(n+1; 1,…,n+1) = ∑_r α(n; [n+1]∖{r+1})` and `α(n+2; 1,…,n+1,n+1) = α(n+1; 1,…,n+1)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false

namespace MT

open Finset

/-- The arithmetic row `(c, c+1, …, c+m-1)`. -/
def ap (m : ℕ) (c : ℤ) : Fin m → ℤ := fun i => c + (i : ℕ)

lemma init_ap (m : ℕ) (c : ℤ) : Fin.init (ap (m + 1) c) = ap m c := by
  funext i; simp [Fin.init, ap]

lemma ap_last (m : ℕ) (c : ℤ) : ap (m + 1) c (Fin.last m) = c + m := by simp [ap]

lemma del_castSucc {m : ℕ} (k : Fin (m + 2) → ℤ) (r : Fin (m + 1)) :
    (fun i => k ((Fin.castSucc r).succAbove i))
      = (Fin.snoc (fun i => Fin.init k (r.succAbove i)) (k (Fin.last _)) : Fin (m + 1) → ℤ) := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last, Fin.succAbove_of_le_castSucc _ _ (by simpa using Fin.le_last r), Fin.succ_last]
  | cast i =>
    rw [Fin.snoc_castSucc, Fin.castSucc_succAbove_castSucc]; rfl

lemma del_last {m : ℕ} (k : Fin (m + 1) → ℤ) :
    (fun i => k ((Fin.last m).succAbove i)) = Fin.init k := by
  funext i; rw [Fin.succAbove_last]; rfl

theorem S_ap : ∀ (n : ℕ) (c : ℤ) (A : (Fin n → ℤ) → ℚ),
    S n (ap (n + 1) c) A = ∑ r : Fin (n + 1), A (fun i => ap (n + 1) c (r.succAbove i))
  | 0, c, A => by
    simp only [S]
    rw [Fin.sum_univ_one]
    congr 1; funext i; exact i.elim0
  | 1, c, A => by
    simp only [S]
    rw [Fin.sum_univ_two]
    have a1 : (0 : Fin 2).succAbove (0 : Fin 1) = 1 := by decide
    have a2 : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := by decide
    have f1 : (fun i : Fin 1 => ap (1 + 1) c ((0 : Fin 2).succAbove i)) = fun _ => c + 1 :=
      fin1_eq _ _ (by show ap (1 + 1) c ((0 : Fin 2).succAbove 0) = c + 1; rw [a1]; simp [ap])
    have f2 : (fun i : Fin 1 => ap (1 + 1) c ((1 : Fin 2).succAbove i)) = fun _ => c :=
      fin1_eq _ _ (by show ap (1 + 1) c ((1 : Fin 2).succAbove 0) = c; rw [a2]; simp [ap])
    have h0 : ap 2 c 0 = c := by simp [ap]
    have h1 : ap 2 c 1 = c + 1 := by simp [ap]
    rw [f1, f2, h0, h1]
    unfold ssum
    have hI : Ico c (c + 1 + 1) = {c, c + 1} := by
      ext x; simp only [mem_Ico, mem_insert, mem_singleton]; omega
    rw [hI, Ico_eq_empty_of_le (by omega), sum_pair (by omega), sum_empty, sub_zero, add_comm]
  | n + 2, c, A => by
    simp only [S]
    rw [init_ap, init_ap]
    have hl : ap (n + 3) c (Fin.last (n + 2)) = ap (n + 3) c (Fin.last (n + 1)).castSucc + 1 := by
      simp [ap]; ring
    set x := ap (n + 3) c (Fin.last (n + 1)).castSucc with hx
    have hx' : x = c + (n + 1 : ℕ) := by simp [hx, ap]
    rw [hl]
    unfold ssum
    have hI : Ico x (x + 1 + 1) = {x, x + 1} := by
      ext y; simp only [mem_Ico, mem_insert, mem_singleton]; omega
    have hE : Ico (x + 1 + 1) x = ∅ := Ico_eq_empty_of_le (by omega)
    rw [hI, hE, sum_pair (by omega), sum_empty, sub_zero]
    rw [S_ap (n + 1) c, S_ap (n + 1) c, S_ap n c]
    rw [Fin.sum_univ_castSucc (n := n + 2), Fin.sum_univ_castSucc (n := n + 1)]
    have hlast : ap (n + 2) c (Fin.last (n + 1)) = x := by simp [hx, ap]
    have e1 : ∀ r : Fin (n + 1), (Fin.snoc (fun i => ap (n + 2) c ((Fin.castSucc r).succAbove i)) x
        : Fin (n + 2) → ℤ)
        = Fin.snoc (Fin.snoc (fun i => ap (n + 1) c (r.succAbove i)) x : Fin (n + 1) → ℤ) x := by
      intro r
      rw [del_castSucc (ap (n + 2) c) r, init_ap, hlast]
    have e2 : (Fin.snoc (fun i => ap (n + 2) c ((Fin.last (n + 1)).succAbove i)) x
        : Fin (n + 2) → ℤ) = fun i => ap (n + 3) c ((Fin.last (n + 2)).succAbove i) := by
      rw [del_last, del_last, init_ap, init_ap]
      funext i
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last, hx]; simp [ap]
      | cast i => rw [Fin.snoc_castSucc]; simp [ap]
    have e3 : ∀ r : Fin (n + 2), (Fin.snoc (fun i => ap (n + 2) c (r.succAbove i)) (x + 1)
        : Fin (n + 2) → ℤ) = fun i => ap (n + 3) c ((Fin.castSucc r).succAbove i) := by
      intro r
      rw [del_castSucc (ap (n + 3) c) r, init_ap, ap_last]
      congr 1; rw [hx']; push_cast; ring
    simp only [e1, e2, e3]
    ring

theorem S_apdup (n : ℕ) (c : ℤ) (A : (Fin (n + 1) → ℤ) → ℚ) :
    S (n + 1) (Fin.snoc (ap (n + 1) c) (c + n) : Fin (n + 2) → ℤ) A = A (ap (n + 1) c) := by
  cases n with
  | zero =>
    simp only [S]
    unfold ssum
    have h0 : (Fin.snoc (ap 1 c) (c + (0 : ℕ)) : Fin 2 → ℤ) 0 = c := by
      simp [Fin.snoc, ap]
    have h1 : (Fin.snoc (ap 1 c) (c + (0 : ℕ)) : Fin 2 → ℤ) 1 = c := by
      simp [Fin.snoc]
    rw [h0, h1]
    have hI : Ico c (c + 1) = {c} := by ext y; simp only [mem_Ico, mem_singleton]; omega
    rw [hI, Ico_eq_empty_of_le (by omega), sum_singleton, sum_empty, sub_zero]
    congr 1; funext i; rw [Fin.fin_one_eq_zero i]; simp [ap]
  | succ m =>
    simp only [S]
    rw [Fin.init_snoc, init_ap]
    have hc1 : (Fin.snoc (ap (m + 2) c) (c + (m + 1 : ℕ)) : Fin (m + 3) → ℤ) (Fin.last (m + 1)).castSucc
        = c + (m + 1 : ℕ) := by
      rw [Fin.snoc_castSucc, ap_last]
    have hc2 : (Fin.snoc (ap (m + 2) c) (c + (m + 1 : ℕ)) : Fin (m + 3) → ℤ) (Fin.last (m + 2))
        = c + (m + 1 : ℕ) := Fin.snoc_last _ _
    rw [hc1, hc2]
    set x : ℤ := c + (m + 1 : ℕ) with hx
    unfold ssum
    have hI : Ico x (x + 1) = {x} := by ext y; simp only [mem_Ico, mem_singleton]; omega
    rw [hI, Ico_eq_empty_of_le (by omega), sum_singleton, sum_empty, sub_zero]
    rw [S_ap (m + 1) c, S_ap m c, Fin.sum_univ_castSucc]
    have hlast : ap (m + 2) c (Fin.last (m + 1)) = x := by rw [ap_last]
    have e1 : ∀ r : Fin (m + 1), (Fin.snoc (fun i => ap (m + 2) c ((Fin.castSucc r).succAbove i)) x
        : Fin (m + 2) → ℤ)
        = Fin.snoc (Fin.snoc (fun i => ap (m + 1) c (r.succAbove i)) x : Fin (m + 1) → ℤ) x := by
      intro r
      rw [del_castSucc (ap (m + 2) c) r, init_ap, hlast]
    have e2 : (Fin.snoc (fun i => ap (m + 2) c ((Fin.last (m + 1)).succAbove i)) x
        : Fin (m + 2) → ℤ) = ap (m + 2) c := by
      rw [del_last, init_ap]
      funext i
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last, hlast]
      | cast i => rw [Fin.snoc_castSucc]; simp [ap]
    simp only [e1, e2]
    ring

/-- `α(n+1; 1,…,n+1) = ∑_r α(n; (1,…,n+1) without its r-th entry)`. -/
theorem alpha_ap (n : ℕ) (c : ℤ) :
    alpha (n + 1) (ap (n + 1) c) = ∑ r : Fin (n + 1), alpha n (fun i => ap (n + 1) c (r.succAbove i)) := by
  rw [alpha_rec, S_ap]

/-- `α(n+2; c,…,c+n,c+n) = α(n+1; c,…,c+n)`. -/
theorem alpha_apdup (n : ℕ) (c : ℤ) :
    alpha (n + 2) (Fin.snoc (ap (n + 1) c) (c + n)) = alpha (n + 1) (ap (n + 1) c) := by
  rw [alpha_rec, S_apdup]

end MT
```

### `MTCert.lean`

```lean
import MTAct

/-!
# A verified checker for window identities

Given a finite list `L` of (window row, coefficient) pairs, `check` expands
`∑ c · (∏_{s<t} T_{s,t} h)(y)` into `∑ c' h(y')`, rewrites each `h(y')` as `± h(sorted y')` (or `0`
if `y'` has a repeated entry) using the antisymmetry of `h`, and checks that all coefficients cancel.
`cert_sound` proves: if the check succeeds then the identity holds for every antisymmetric `h`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace MT

open Finset

/-- A term: (fast-comparison key, window row as a list of naturals with offset 64), coefficient.
The key is used only to speed up comparisons; soundness never depends on it. -/
abbrev Term := (ℕ × List ℕ) × ℤ

/-- The vector of a list: entry `i` is `l[i] − 64` (missing entries count as `64`, i.e. `0`). -/
def vec {w : ℕ} (v : List ℕ) : Fin w → ℤ := fun i => (v.getD i 64 : ℤ) - 64

/-- Boolean equality of lists of naturals. -/
def lbeq : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && lbeq as bs
  | _, _ => false

lemma lbeq_eq : ∀ a b : List ℕ, lbeq a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [lbeq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, lbeq_eq as bs h.2]
  | [], _ :: _, h => by simp [lbeq] at h
  | _ :: _, [], h => by simp [lbeq] at h

/-- Increment entry `s` (padding with `64`). -/
def bump : ℕ → List ℕ → List ℕ
  | 0, [] => [65]
  | 0, x :: xs => (x + 1) :: xs
  | s + 1, [] => 64 :: bump s []
  | s + 1, x :: xs => x :: bump s xs

lemma getD_bump : ∀ (s : ℕ) (v : List ℕ) (i : ℕ),
    (bump s v).getD i 64 = v.getD i 64 + if i = s then 1 else 0
  | 0, [], 0 => by simp [bump]
  | 0, [], i + 1 => by simp [bump]
  | 0, x :: xs, 0 => by simp [bump]
  | 0, x :: xs, i + 1 => by simp [bump]
  | s + 1, [], 0 => by simp [bump]
  | s + 1, [], i + 1 => by
    rw [show bump (s + 1) [] = 64 :: bump s [] from rfl, List.getD_cons_succ, getD_bump s [] i]
    simp
  | s + 1, x :: xs, 0 => by simp [bump]
  | s + 1, x :: xs, i + 1 => by
    rw [show bump (s + 1) (x :: xs) = x :: bump s xs from rfl, List.getD_cons_succ,
      getD_bump s xs i, List.getD_cons_succ]
    simp

/-- The unit vector `e_s` in `ℤ^w` (zero if `s ≥ w`). -/
def es {w : ℕ} (s : ℕ) : Fin w → ℤ := fun i => if (i : ℕ) = s then 1 else 0

lemma vec_bump {w : ℕ} (s : ℕ) (v : List ℕ) : (vec (bump s v) : Fin w → ℤ) = vec v + es s := by
  funext i; simp only [vec, es, Pi.add_apply]; rw [getD_bump]; split_ifs <;> push_cast <;> ring

/-- Bump the row of a key-row pair (and its key). -/
def bk (s : ℕ) (v : ℕ × List ℕ) : ℕ × List ℕ := (v.1 + 256 ^ s, bump s v.2)

/-- `X_s` and `T_{s,t}` indexed by natural numbers. -/
noncomputable def Xn {w : ℕ} (s : ℕ) : Alg w := AddMonoidAlgebra.single (es s) 1
noncomputable def Tn {w : ℕ} (s t : ℕ) : Alg w := 1 - Xn s + Xn s * Xn t

lemma Xn_eq {w : ℕ} (s : Fin w) : (Xn s : Alg w) = X s := by
  unfold Xn X; congr 1; funext i
  simp only [es, Pi.single_apply, Fin.ext_iff]

lemma Tn_eq {w : ℕ} (s t : Fin w) : (Tn s t : Alg w) = T s t := by
  unfold Tn T; rw [Xn_eq, Xn_eq]

lemma act_Tn_apply {w : ℕ} (s t : ℕ) (h : Fn w) (k : Fin w → ℤ) :
    act w (Tn s t) h k = h k - h (k + es s) + h (k + es s + es t) := by
  unfold Tn
  rw [act_add_apply, map_sub, map_one]
  show (h k - act w (Xn s) h k) + act w (Xn s * Xn t) h k = _
  rw [act_mul_apply]
  simp only [Xn, act_single, one_mul]

/-- `∑_{(·,v,c) ∈ L} c · G(v)`. -/
def evalL (G : List ℕ → ℚ) (L : List Term) : ℚ := (L.map fun u => (u.2 : ℚ) * G u.1.2).sum

lemma evalL_cons (G : List ℕ → ℚ) (u : Term) (L : List Term) :
    evalL G (u :: L) = (u.2 : ℚ) * G u.1.2 + evalL G L := by
  simp [evalL]

lemma evalL_append (G : List ℕ → ℚ) (L M : List Term) :
    evalL G (L ++ M) = evalL G L + evalL G M := by
  simp [evalL]

/-- Insert a term, adding coefficients of equal rows. -/
def insertT (t : Term) : List Term → List Term
  | [] => [t]
  | u :: us => if (Nat.beq u.1.1 t.1.1 && lbeq u.1.2 t.1.2) = true then (u.1, u.2 + t.2) :: us
      else u :: insertT t us

lemma evalL_insertT (G : List ℕ → ℚ) (t : Term) : ∀ L : List Term,
    evalL G (insertT t L) = (t.2 : ℚ) * G t.1.2 + evalL G L
  | [] => by simp [insertT, evalL]
  | u :: us => by
    simp only [insertT]
    split_ifs with h
    · simp only [Bool.and_eq_true] at h
      rw [evalL_cons, evalL_cons, lbeq_eq _ _ h.2]; push_cast; ring
    · rw [evalL_cons, evalL_cons, evalL_insertT G t us]; ring

/-- Merge equal rows. -/
def mergeL (L : List Term) : List Term := L.foldr insertT []

lemma evalL_mergeL (G : List ℕ → ℚ) : ∀ L : List Term, evalL G (mergeL L) = evalL G L
  | [] => rfl
  | u :: L => by
    simp only [mergeL, List.foldr_cons] at *
    rw [evalL_insertT, evalL_cons]
    have := evalL_mergeL G L
    simp only [mergeL] at this
    rw [this]

/-- Multiply by `T_{s,t}`. -/
def mulT (s t : ℕ) (L : List Term) : List Term :=
  mergeL (L.flatMap fun u => [u, (bk s u.1, -u.2), (bk t (bk s u.1), u.2)])

lemma evalL_flatMap (G : List ℕ → ℚ) (f : Term → List Term) : ∀ L : List Term,
    evalL G (L.flatMap f) = (L.map fun u => evalL G (f u)).sum
  | [] => rfl
  | u :: L => by
    rw [List.flatMap_cons, evalL_append, evalL_flatMap G f L]; simp

lemma evalL_mulT {w : ℕ} (s t : ℕ) (h : Fn w) (L : List Term) :
    evalL (fun v => h (vec v)) (mulT s t L) = evalL (fun v => act w (Tn s t) h (vec v)) L := by
  unfold mulT
  rw [evalL_mergeL, evalL_flatMap]
  induction L with
  | nil => rfl
  | cons u L ih =>
    rw [List.map_cons, List.sum_cons, ih, evalL_cons (fun v => act w (Tn s t) h (vec v))]
    congr 1
    simp only [evalL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bk]
    rw [act_Tn_apply, vec_bump, vec_bump, vec_bump]
    push_cast; ring

/-- Multiply by the factors `T_{s,t}` for `(s,t)` in a list. -/
def expandL : List (ℕ × ℕ) → List Term → List Term
  | [], L => L
  | p :: ps, L => expandL ps (mulT p.1 p.2 L)

/-- The product of the `T_{s,t}` for `(s,t)` in a list. -/
noncomputable def prodT {w : ℕ} : List (ℕ × ℕ) → Alg w
  | [] => 1
  | p :: ps => Tn p.1 p.2 * prodT ps

lemma evalL_expand {w : ℕ} : ∀ (ps : List (ℕ × ℕ)) (h : Fn w) (L : List Term),
    evalL (fun v => act w (prodT ps) h (vec v)) L = evalL (fun v => h (vec v)) (expandL ps L)
  | [], h, L => by simp only [prodT, expandL, act_one_apply]
  | p :: ps, h, L => by
    simp only [prodT, expandL, act_mul_apply]
    rw [← evalL_expand ps h (mulT p.1 p.2 L), evalL_mulT]

/-! ## Canonicalization by antisymmetry -/

/-- Swap entries `p` and `p+1` (padding with `64`). -/
def swapAt : ℕ → List ℕ → List ℕ
  | 0, [] => []
  | 0, [x] => [64, x]
  | 0, x :: y :: r => y :: x :: r
  | _ + 1, [] => []
  | p + 1, x :: r => x :: swapAt p r

lemma getD_swapAt : ∀ (p : ℕ) (v : List ℕ) (i : ℕ),
    (swapAt p v).getD i 64 = v.getD (if i = p then p + 1 else if i = p + 1 then p else i) 64
  | 0, [], i => by simp [swapAt]
  | 0, [x], 0 => by simp [swapAt]
  | 0, [x], 1 => by simp [swapAt]
  | 0, [x], i + 2 => by simp [swapAt]
  | 0, x :: y :: r, 0 => by simp [swapAt]
  | 0, x :: y :: r, 1 => by simp [swapAt]
  | 0, x :: y :: r, i + 2 => by simp [swapAt]
  | p + 1, [], i => by simp [swapAt]
  | p + 1, x :: r, 0 => by simp [swapAt]
  | p + 1, x :: r, i + 1 => by
    simp only [swapAt, List.getD_cons_succ]
    rw [getD_swapAt p r i]
    split_ifs <;> first | omega | simp_all

/-- Antisymmetry of `h : ℤ^w → ℚ` under adjacent transpositions. -/
def Antisym (w : ℕ) (h : Fn w) : Prop :=
  ∀ (p : ℕ) (hp : p + 1 < w) (y : Fin w → ℤ),
    h (fun i => y (Equiv.swap ⟨p, by omega⟩ ⟨p + 1, hp⟩ i)) = - h y

lemma vec_swapAt {w : ℕ} (p : ℕ) (hp : p + 1 < w) (v : List ℕ) :
    (vec (swapAt p v) : Fin w → ℤ) = fun i => vec v (Equiv.swap ⟨p, by omega⟩ ⟨p + 1, hp⟩ i) := by
  funext i
  simp only [vec, getD_swapAt, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all [Fin.ext_iff] <;> omega

/-- One compare-and-swap step at positions `p, p+1`. -/
def step (p : ℕ) (u : List ℕ × ℤ) : Option (List ℕ × ℤ) :=
  if Nat.blt (u.1.getD p 64) (u.1.getD (p + 1) 64) = true then some u
  else if Nat.beq (u.1.getD p 64) (u.1.getD (p + 1) 64) = true then none
  else some (swapAt p u.1, -u.2)

/-- Value of an optional term. -/
def optVal (G : List ℕ → ℚ) : Option (List ℕ × ℤ) → ℚ
  | none => 0
  | some u => (u.2 : ℚ) * G u.1

lemma step_sound {w : ℕ} (h : Fn w) (hh : Antisym w h) (p : ℕ) (hp : p + 1 < w)
    (u : List ℕ × ℤ) : optVal (fun v => h (vec v)) (step p u) = (u.2 : ℚ) * h (vec u.1) := by
  unfold step
  split_ifs with h1 h2
  · rfl
  · rw [Nat.beq_eq] at h2
    have hfix : (fun i => (vec u.1 : Fin w → ℤ) (Equiv.swap ⟨p, by omega⟩ ⟨p + 1, hp⟩ i))
        = vec u.1 := by
      rw [← vec_swapAt p hp]
      funext i
      simp only [vec, getD_swapAt]
      split_ifs with a b
      · rw [a, h2]
      · rw [b, h2]
      · rfl
    have := hh p hp (vec u.1)
    rw [hfix] at this
    have h0 : h (vec u.1) = 0 := by linarith
    simp [optVal, h0]
  · simp only [optVal]
    rw [vec_swapAt p hp, hh p hp]
    push_cast; ring

/-- Canonicalize a row by a list of compare-and-swap steps. -/
def canonT : List ℕ → List ℕ × ℤ → Option (List ℕ × ℤ)
  | [], u => some u
  | p :: ps, u => (step p u).bind (canonT ps)

lemma canonT_sound {w : ℕ} (h : Fn w) (hh : Antisym w h) : ∀ (ps : List ℕ),
    (∀ p ∈ ps, p + 1 < w) → ∀ u : List ℕ × ℤ,
    optVal (fun v => h (vec v)) (canonT ps u) = (u.2 : ℚ) * h (vec u.1)
  | [], _, u => rfl
  | p :: ps, hps, u => by
    have hs := step_sound h hh p (hps p (List.mem_cons_self ..)) u
    simp only [canonT]
    cases hst : step p u with
    | none => rw [hst] at hs; simpa [optVal] using hs
    | some u' =>
      rw [hst] at hs
      simp only [Option.bind_some]
      rw [canonT_sound h hh ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) u']
      exact hs

/-- The key of a row (only used for fast comparisons). -/
def enc (l : List ℕ) : ℕ := l.foldr (fun x acc => x + 256 * acc) 0

/-- Canonicalize a term and recompute its key. -/
def canonA (ps : List ℕ) (u : Term) : Option Term :=
  (canonT ps (u.1.2, u.2)).map fun v => ((enc v.1, v.1), v.2)

lemma evalL_filterMap_canon {w : ℕ} (h : Fn w) (hh : Antisym w h) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p + 1 < w) : ∀ L : List Term,
    evalL (fun v => h (vec v)) (L.filterMap (canonA ps)) = evalL (fun v => h (vec v)) L
  | [] => rfl
  | u :: L => by
    have hs := canonT_sound h hh ps hps (u.1.2, u.2)
    rw [List.filterMap_cons, evalL_cons,
      show canonA ps u = (canonT ps (u.1.2, u.2)).map (fun v => ((enc v.1, v.1), v.2)) from rfl]
    cases hc : canonT ps (u.1.2, u.2) with
    | none =>
      rw [hc] at hs
      simp only [Option.map_none]
      rw [evalL_filterMap_canon h hh ps hps L]
      simp only [optVal] at hs
      rw [← hs, zero_add]
    | some v =>
      rw [hc] at hs
      simp only [Option.map_some, evalL_cons]
      rw [evalL_filterMap_canon h hh ps hps L]
      simp only [optVal] at hs
      rw [hs]

/-- Canonicalize and merge. -/
def canonL (ps : List ℕ) (L : List Term) : List Term := mergeL (L.filterMap (canonA ps))

lemma evalL_canonL {w : ℕ} (h : Fn w) (hh : Antisym w h) (ps : List ℕ)
    (hps : ∀ p ∈ ps, p + 1 < w) (L : List Term) :
    evalL (fun v => h (vec v)) (canonL ps L) = evalL (fun v => h (vec v)) L := by
  unfold canonL
  rw [evalL_mergeL, evalL_filterMap_canon h hh ps hps]

lemma evalL_allzero (G : List ℕ → ℚ) : ∀ L : List Term,
    L.all (fun u => u.2 == 0) = true → evalL G L = 0
  | [], _ => rfl
  | u :: L, hL => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hL
    rw [evalL_cons, hL.1, evalL_allzero G L (by simpa using hL.2)]
    simp

/-- The certificate check. -/
def check (w : ℕ) (ps : List ℕ) (pairs : List (ℕ × ℕ)) (L : List Term) : Bool :=
  ps.all (fun p => decide (p + 1 < w)) && (canonL ps (expandL pairs L)).all (fun u => u.2 == 0)

/-- **Soundness of the checker.** -/
theorem cert_sound (w : ℕ) (ps : List ℕ) (pairs : List (ℕ × ℕ)) (L : List Term)
    (hc : check w ps pairs L = true) (h : Fn w) (hh : Antisym w h) :
    evalL (fun v => act w (prodT pairs) h (vec v)) L = 0 := by
  unfold check at hc
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  rw [evalL_expand, ← evalL_canonL h hh ps hc.1]
  exact evalL_allzero _ _ (List.all_eq_true.mpr hc.2)

/-! ## Window certificates (window coordinates, base point `a = 0`; entries carry offset 64) -/

def pairs2 : List (ℕ × ℕ) := [(0, 1)]
def pairs3 : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2)]
def pairs4 : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)]

/-- A term from a row and coefficient. -/
def mk (l : List ℕ) (c : ℤ) : Term := ((enc l, l), c)

/-- W2: `α(…,a,a,a+1,…) − α(…,a,a+1,a+1,…) = 0`. -/
def certW2 : List Term := [mk [64, 64, 65] 1, mk [64, 65, 65] (-1)]
/-- W4: `W(a+1,a)+W(a,a−1)−W(a,a)+W(a−1,a)+W(a,a+1)−W(a−1,a+1) = 0`. -/
def certW4 : List Term :=
  [mk [65, 64] 1, mk [64, 63] 1, mk [64, 64] (-1), mk [63, 64] 1, mk [64, 65] 1, mk [63, 65] (-1)]

theorem checkW2 : check 3 [0, 1, 0] pairs3 certW2 = true := by decide +kernel
theorem checkW4 : check 2 [0] pairs2 certW4 = true := by decide +kernel

/-- Control: the checker rejects the 3-entry truncation of W1. -/
theorem check_ctrl1 :
    check 3 [0, 1, 0] pairs3 [mk [64, 66, 65] 1, mk [65, 64, 65] (-1), mk [64, 64, 65] (-1)] = false := by
  decide +kernel

end MT
```

### `MTCertW1.lean`

```lean
import MTCert

/-! # Certificate W1 (kernel-checked by `decide +kernel`) -/

namespace MT

/-- W1: `α(…,a,a+2,a+1,a+2,…) − α(…,a+1,a,a+1,a+2,…) − α(…,a,a,a+1,a+2,…) = 0`. -/
def certW1 : List Term := [mk [64, 66, 65, 66] 1, mk [65, 64, 65, 66] (-1), mk [64, 64, 65, 66] (-1)]

theorem checkW1 : check 4 [0, 1, 2, 0, 1, 0] pairs4 certW1 = true := by decide +kernel

end MT
```

### `MTCertW3.lean`

```lean
import MTCert

/-! # Certificate W3 and a negative control (kernel-checked by `decide +kernel`) -/

namespace MT

/-- W3: `α(…,a,a,a+2,a+2,…) − α(…,a,a,a+1,a+2,…) = 0`. -/
def certW3 : List Term := [mk [64, 64, 66, 66] 1, mk [64, 64, 65, 66] (-1)]

theorem checkW3 : check 4 [0, 1, 2, 0, 1, 0] pairs4 certW3 = true := by decide +kernel

/-- Control: the checker rejects W1 with its last entry `a+2` replaced by `a+3`. -/
theorem check_ctrl2 : check 4 [0, 1, 2, 0, 1, 0] pairs4
    [mk [64, 66, 65, 67] 1, mk [65, 64, 65, 67] (-1), mk [64, 64, 65, 67] (-1)] = false := by
  decide +kernel

end MT
```

### `MTWindow.lean`

```lean
import MTRec
import MTCert

/-!
# The window principle

For a block `W = {s0, …, s0+w−1}` of consecutive positions, Fischer's operator splits as
`Q2 N = QW · QO`, where `QO` (pairs not inside `W`) commutes with the transpositions of adjacent
positions of `W`, so `F = QO · Fdet` is antisymmetric in the window coordinates, while `QW` is the
`w`-variable operator acting on the window coordinates.  Hence every certified window identity
holds at every position and in every context.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace MT

open Finset

variable {N w : ℕ}

/-- `ins s0 k y`: the row `k` with positions `s0, …, s0+w−1` replaced by `y`. -/
def ins (s0 : ℕ) (k : Fin N → ℤ) (y : Fin w → ℤ) : Fin N → ℤ :=
  fun p => if h : s0 ≤ (p : ℕ) ∧ (p : ℕ) < s0 + w then y ⟨p - s0, by omega⟩ else k p

/-- Position `s0 + i` of the window. -/
def wpos (s0 : ℕ) (hw : s0 + w ≤ N) (i : Fin w) : Fin N := ⟨s0 + i, by omega⟩

/-- Membership in the window. -/
def inW (s0 w : ℕ) (s : Fin N) : Prop := s0 ≤ (s : ℕ) ∧ (s : ℕ) < s0 + w

instance (s0 w : ℕ) (s : Fin N) : Decidable (inW s0 w s) := by unfold inW; infer_instance

lemma ins_add (s0 : ℕ) (k : Fin N → ℤ) (y v : Fin w → ℤ) :
    ins s0 k (y + v) = ins s0 k y + ins s0 0 v := by
  funext p; simp only [ins, Pi.add_apply]; split_ifs <;> simp

lemma ins_single (s0 : ℕ) (hw : s0 + w ≤ N) (i : Fin w) :
    (ins s0 (0 : Fin N → ℤ) (Pi.single i 1) : Fin N → ℤ) = Pi.single (wpos s0 hw i) 1 := by
  funext p
  simp only [ins, wpos, Pi.single_apply, Fin.ext_iff, Pi.zero_apply]
  split_ifs <;> first | rfl | omega

lemma Fdet_swap (n : ℕ) (i j : Fin n) (hij : i ≠ j) (l : Fin n → ℤ) :
    Fdet n (fun r => l (Equiv.swap i j r)) = - Fdet n l := by
  unfold Fdet
  have := Matrix.det_permute (Equiv.swap i j) (Matrix.of fun r c : Fin n => bin c (l r))
  rw [Equiv.Perm.sign_swap hij] at this
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at this
  rw [← this]
  rfl

/-! ## Splitting the operator -/

/-- Pairs inside the window. -/
noncomputable def QW (s0 w N : ℕ) : Alg N :=
  ∏ t : Fin N, ∏ s : Fin N, if s < t ∧ inW s0 w s ∧ inW s0 w t then T s t else 1

/-- Pairs not inside the window. -/
noncomputable def QO (s0 w N : ℕ) : Alg N :=
  ∏ t : Fin N, ∏ s : Fin N, if s < t ∧ ¬(inW s0 w s ∧ inW s0 w t) then T s t else 1

lemma Q2_split (s0 w N : ℕ) : Q2 N = QW s0 w N * QO s0 w N := by
  unfold Q2 QW QO
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun t _ => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun s _ => ?_
  by_cases h1 : s < t <;> by_cases h2 : (inW s0 w s ∧ inW s0 w t) <;> simp [h1, h2]

lemma prod_window (s0 : ℕ) (hw : s0 + w ≤ N) (H : Fin N → Alg N)
    (hH : ∀ t : Fin N, ¬ inW s0 w t → H t = 1) : ∏ t, H t = ∏ t' : Fin w, H (wpos s0 hw t') := by
  have hinj : Function.Injective (wpos s0 hw) := by
    intro a b h; simp only [wpos, Fin.ext_iff] at h; exact Fin.ext (by omega)
  rw [show (∏ t' : Fin w, H (wpos s0 hw t')) = ∏ x ∈ univ.map ⟨wpos s0 hw, hinj⟩, H x from
    (Finset.prod_map univ ⟨wpos s0 hw, hinj⟩ H).symm]
  symm
  apply Finset.prod_subset (subset_univ _)
  intro x _ hx
  apply hH
  intro hW
  apply hx
  simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
  exact ⟨⟨x - s0, by unfold inW at hW; omega⟩, by
    simp only [wpos, Fin.ext_iff]; unfold inW at hW; omega⟩

lemma inW_wpos (s0 : ℕ) (hw : s0 + w ≤ N) (i : Fin w) : inW s0 w (wpos s0 hw i) := by
  unfold inW wpos; simp only; omega

lemma QW_eq (s0 : ℕ) (hw : s0 + w ≤ N) :
    QW s0 w N = ∏ t' : Fin w, ∏ s' : Fin w,
      if s' < t' then T (wpos s0 hw s') (wpos s0 hw t') else 1 := by
  unfold QW
  rw [prod_window s0 hw]
  · refine prod_congr rfl fun t' _ => ?_
    rw [prod_window s0 hw]
    · refine prod_congr rfl fun s' _ => ?_
      have hlt : (wpos s0 hw s' < wpos s0 hw t') ↔ s' < t' := by
        simp only [wpos, Fin.lt_iff_val_lt_val]; omega
      simp only [hlt, inW_wpos, and_true]
    · intro s hs; simp [hs]
  · intro t ht
    apply prod_eq_one
    intro s _
    simp [ht]

/-! ## Transport along the window embedding -/

/-- `P` acting at `ins s0 k y` equals `P'` acting on `y ↦ F (ins s0 k y)`. -/
def RelW (s0 : ℕ) (k : Fin N → ℤ) (P' : Alg w) (P : Alg N) : Prop :=
  ∀ (F : Fn N) (y : Fin w → ℤ), act N P F (ins s0 k y) = act w P' (fun y' => F (ins s0 k y')) y

namespace RelW

variable {s0 : ℕ} {k : Fin N → ℤ}

lemma single (v : Fin w → ℤ) (c : ℚ) :
    RelW s0 k (AddMonoidAlgebra.single v c) (AddMonoidAlgebra.single (ins s0 0 v) c) := by
  intro F y
  rw [act_single, act_single, ins_add]

lemma one : RelW s0 k (1 : Alg w) (1 : Alg N) := by
  intro F y; rw [act_one_apply, act_one_apply]

lemma add {P' Q' : Alg w} {P Q : Alg N} (h : RelW s0 k P' P) (h' : RelW s0 k Q' Q) :
    RelW s0 k (P' + Q') (P + Q) := by
  intro F y; rw [act_add_apply, act_add_apply, h, h']

lemma neg {P' : Alg w} {P : Alg N} (h : RelW s0 k P' P) : RelW s0 k (-P') (-P) := by
  intro F y
  have e1 : act N (-P) = - act N P := map_neg _ _
  have e2 : act w (-P') = - act w P' := map_neg _ _
  rw [e1, e2]
  show - (act N P F (ins s0 k y)) = - (act w P' (fun y' => F (ins s0 k y')) y)
  rw [h]

lemma sub {P' Q' : Alg w} {P Q : Alg N} (h : RelW s0 k P' P) (h' : RelW s0 k Q' Q) :
    RelW s0 k (P' - Q') (P - Q) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h.add h'.neg

lemma mul {P' Q' : Alg w} {P Q : Alg N} (h : RelW s0 k P' P) (h' : RelW s0 k Q' Q) :
    RelW s0 k (P' * Q') (P * Q) := by
  intro F y
  rw [act_mul_apply, act_mul_apply, h]
  exact congrArg (fun G => act w P' G y) (funext fun y' => h' F y')

lemma ite {P' : Alg w} {P : Alg N} (c : Prop) [Decidable c] (h : RelW s0 k P' P) :
    RelW s0 k (if c then P' else 1) (if c then P else 1) := by
  split_ifs
  · exact h
  · exact one

lemma prod {ι : Type*} (s : Finset ι) (P' : ι → Alg w) (P : ι → Alg N)
    (h : ∀ x ∈ s, RelW s0 k (P' x) (P x)) : RelW s0 k (∏ x ∈ s, P' x) (∏ x ∈ s, P x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one : RelW s0 k (1 : Alg w) (1 : Alg N))
  | insert x s hx ih =>
    rw [prod_insert hx, prod_insert hx]
    exact (h x (mem_insert_self x s)).mul (ih fun y hy => h y (mem_insert_of_mem hy))

end RelW

lemma relW_T (s0 : ℕ) (hw : s0 + w ≤ N) (k : Fin N → ℤ) (s t : Fin w) :
    RelW s0 k (T s t) (T (wpos s0 hw s) (wpos s0 hw t)) := by
  have hX : ∀ i : Fin w, RelW s0 k (X i) (X (wpos s0 hw i)) := by
    intro i
    have := RelW.single (s0 := s0) (k := k) (Pi.single i (1 : ℤ)) (1 : ℚ)
    rwa [ins_single s0 hw] at this
  exact (RelW.one.sub (hX s)).add ((hX s).mul (hX t))

lemma relW_QW (s0 : ℕ) (hw : s0 + w ≤ N) (k : Fin N → ℤ) : RelW s0 k (Q2 w) (QW s0 w N) := by
  rw [QW_eq s0 hw, Q2]
  exact RelW.prod univ _ _ fun t _ => RelW.prod univ _ _ fun s _ =>
    RelW.ite (s < t) (relW_T s0 hw k s t)

/-! ## Antisymmetry of `QO · Fdet` in the window coordinates -/

lemma cond_swap (s0 : ℕ) (hw : s0 + w ≤ N) (p : ℕ) (hp : p + 1 < w) (s t : Fin N) :
    let τ := Equiv.swap (⟨s0 + p, by omega⟩ : Fin N) ⟨s0 + p + 1, by omega⟩
    (τ s < τ t ∧ ¬(inW s0 w (τ s) ∧ inW s0 w (τ t))) ↔ (s < t ∧ ¬(inW s0 w s ∧ inW s0 w t)) := by
  intro τ
  simp only [τ, Equiv.swap_apply_def, inW, Fin.lt_iff_val_lt_val]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [Fin.ext_iff] at * <;> omega

lemma QO_antisym (s0 : ℕ) (hw : s0 + w ≤ N) (p : ℕ) (hp : p + 1 < w) (m : Fin N → ℤ) :
    act N (QO s0 w N) (Fdet N)
        (permHom (Equiv.swap (⟨s0 + p, by omega⟩ : Fin N) ⟨s0 + p + 1, by omega⟩) m)
      = - act N (QO s0 w N) (Fdet N) m := by
  set τ := Equiv.swap (⟨s0 + p, by omega⟩ : Fin N) ⟨s0 + p + 1, by omega⟩ with hτ
  have hne : (⟨s0 + p, by omega⟩ : Fin N) ≠ ⟨s0 + p + 1, by omega⟩ := by
    simp [Fin.ext_iff]
  have hsymm : τ.symm = τ := Equiv.symm_swap _ _
  have hrel : Rel (permHom τ)
      (∏ t : Fin N, ∏ s : Fin N, if s < t ∧ ¬(inW s0 w s ∧ inW s0 w t) then T (τ s) (τ t) else 1)
      (QO s0 w N) := by
    have := Rel.prod univ _ _ fun t _ => Rel.prod univ _ _ fun s _ =>
      Rel.ite (s < t ∧ ¬(inW s0 w s ∧ inW s0 w t)) (rel_perm_T τ s t)
    rw [hsymm] at this
    exact this
  have hQ : (∏ t : Fin N, ∏ s : Fin N,
      if s < t ∧ ¬(inW s0 w s ∧ inW s0 w t) then T (τ s) (τ t) else 1) = QO s0 w N := by
    have step1 : (∏ t : Fin N, ∏ s : Fin N,
        if s < t ∧ ¬(inW s0 w s ∧ inW s0 w t) then T (τ s) (τ t) else 1)
        = ∏ t : Fin N, ∏ s : Fin N, (fun s t => if τ s < τ t ∧ ¬(inW s0 w (τ s) ∧ inW s0 w (τ t))
            then T s t else (1 : Alg N)) (τ s) (τ t) := by
      refine prod_congr rfl fun t _ => prod_congr rfl fun s _ => ?_
      simp only [hτ, Equiv.swap_apply_self]
    refine step1.trans ((prod_prod_perm τ (fun s t => if τ s < τ t ∧
      ¬(inW s0 w (τ s) ∧ inW s0 w (τ t)) then T s t else (1 : Alg N))).trans ?_)
    unfold QO
    refine prod_congr rfl fun t _ => prod_congr rfl fun s _ => ?_
    have h1 := cond_swap s0 hw p hp s t
    simp only at h1
    rw [← hτ] at h1
    simp only [h1]
  have := hrel (Fdet N) m
  rw [hQ] at this
  have hF : (fun m' => Fdet N (permHom τ m')) = fun m' => - Fdet N m' :=
    funext fun m' => Fdet_swap N _ _ hne m'
  rw [hF, act_fun_neg] at this
  linarith

lemma ins_perm (s0 : ℕ) (hw : s0 + w ≤ N) (p : ℕ) (hp : p + 1 < w) (k : Fin N → ℤ)
    (z : Fin w → ℤ) :
    ins s0 k (fun i => z (Equiv.swap ⟨p, by omega⟩ ⟨p + 1, hp⟩ i))
      = permHom (Equiv.swap (⟨s0 + p, by omega⟩ : Fin N) ⟨s0 + p + 1, by omega⟩) (ins s0 k z) := by
  funext q
  simp only [ins, permHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.swap_apply_def]
  split_ifs <;> first
    | rfl
    | (congr 1; ext; simp_all [Fin.ext_iff]; omega)
    | (exfalso; simp_all [Fin.ext_iff]; omega)
    | (simp_all [Fin.ext_iff])

/-- **Window principle.**  If a list `L` of window rows with coefficients is certified (for every
antisymmetric `h`), then `∑ c · α(N; k with positions s0..s0+w−1 replaced by y + a)` vanishes
for every length `N`, position `s0`, context `k` and shift `a`. -/
theorem window_identity (s0 : ℕ) (hw : s0 + w ≤ N) (pairs : List (ℕ × ℕ))
    (hQ : Q2 w = prodT pairs) (L : List Term)
    (hL : ∀ h : Fn w, Antisym w h → evalL (fun v => act w (prodT pairs) h (vec v)) L = 0)
    (k : Fin N → ℤ) (a : ℤ) :
    (L.map fun u => (u.2 : ℚ) * alpha N (ins s0 k ((vec u.1.2 : Fin w → ℤ) + fun _ => a))).sum
      = 0 := by
  set F := act N (QO s0 w N) (Fdet N) with hFdef
  have hα : ∀ y, alpha N (ins s0 k y) = act w (Q2 w) (fun y' => F (ins s0 k y')) y := by
    intro y
    rw [alpha_eq_Q2, show Pi' N = Fdet N from funext (Pi'_eq_Fdet N), Q2_split s0 w N,
      act_mul_apply]
    exact relW_QW s0 hw k F y
  set g : Fn w := fun y => F (ins s0 k (y + fun _ => a)) with hgdef
  have hg : Antisym w g := by
    intro p hp y
    simp only [hgdef]
    have e : ((fun i => y (Equiv.swap ⟨p, by omega⟩ ⟨p + 1, hp⟩ i)) + fun _ => a)
        = fun i => ((y + fun _ => a) : Fin w → ℤ) (Equiv.swap ⟨p, by omega⟩ ⟨p + 1, hp⟩ i) := by
      funext i; simp
    rw [e, ins_perm s0 hw p hp k, hFdef, QO_antisym s0 hw p hp]
  have := hL g hg
  rw [← hQ] at this
  unfold evalL at this
  rw [← this]
  congr 1
  apply List.map_congr_left
  intro u _
  rw [hα, act_translate]

end MT
```

### `MTSym.lean`

```lean
import MTRec
import Mathlib.Tactic.LinearCombination

/-!
# Translation and reflection symmetry of the operator formula

`α(N; k_1 + c, …, k_N + c) = α(N; k)` and `α(N; −k_N, …, −k_1) = α(N; k)`
(Fischer–Riegler, arXiv:1111.2695, Lemma 5 (2),(3)), proved here for the operator formula.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace MT

open Finset

theorem alpha_translate (N : ℕ) (k : Fin N → ℤ) (c : ℤ) :
    alpha N (k + fun _ => c) = alpha N k := by
  rw [alpha_eq_Q2, alpha_eq_Q2, act_translate]
  refine congrArg (fun G => act N (Q2 N) G k) (funext fun m => ?_)
  unfold Pi'
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  simp only [Pi.add_apply]; push_cast; ring_nf

/-- `k ↦ (−k_N, …, −k_1)`. -/
def reflHom (N : ℕ) : (Fin N → ℤ) →+ (Fin N → ℤ) where
  toFun k := fun p => - k (Fin.rev p)
  map_zero' := by funext p; simp
  map_add' a b := by funext p; simp; ring

lemma Pi'_ite (N : ℕ) (k : Fin N → ℤ) :
    Pi' N k = ∏ i : Fin N, ∏ j : Fin N,
      if i < j then (((k j : ℚ) - k i) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) else 1 := by
  unfold Pi'
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_filter]
  congr 1
  ext j; simp

lemma Pi'_refl (N : ℕ) (k : Fin N → ℤ) : Pi' N (reflHom N k) = Pi' N k := by
  rw [Pi'_ite, Pi'_ite, prod_comm]
  rw [← Equiv.prod_comp Fin.revPerm]
  refine prod_congr rfl fun j _ => ?_
  rw [← Equiv.prod_comp Fin.revPerm]
  refine prod_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, reflHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.rev_rev,
    Fin.rev_lt_rev]
  split_ifs with h
  · have e : (((Fin.rev j : ℕ) : ℚ) - ((Fin.rev i : ℕ) : ℚ)) = ((i : ℕ) : ℚ) - ((j : ℕ) : ℚ) := by
      have hi := i.isLt
      have hj := j.isLt
      rw [Fin.val_rev, Fin.val_rev, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    rw [e]; push_cast; ring
  · rfl

/-- `Z_s`: the image of `X_s` under reflection. -/
noncomputable def Zr (N : ℕ) (s : Fin N) : Alg N :=
  AddMonoidAlgebra.single (reflHom N (Pi.single s 1)) 1

lemma Zr_mul_X (N : ℕ) (s : Fin N) : Zr N s * X (Fin.rev s) = 1 := by
  unfold Zr X
  rw [AddMonoidAlgebra.single_mul_single, one_mul]
  have : reflHom N (Pi.single s 1) + Pi.single (Fin.rev s) 1 = 0 := by
    funext q
    simp only [reflHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.add_apply, Pi.zero_apply,
      Pi.single_apply]
    by_cases h : q = Fin.rev s
    · subst h; simp
    · have h' : Fin.rev q ≠ s := by intro e; apply h; rw [← e, Fin.rev_rev]
      simp [h, h']
  rw [this]; rfl

lemma refl_factor (N : ℕ) (s t : Fin N) :
    1 - Zr N s + Zr N s * Zr N t = Zr N s * Zr N t * T (Fin.rev t) (Fin.rev s) := by
  unfold T
  have h1 := Zr_mul_X N s
  have h2 := Zr_mul_X N t
  linear_combination Zr N s * h2 - (Zr N t * X t.rev) * h1 - h2

lemma refl_single_apply (N : ℕ) (s q : Fin N) :
    reflHom N (Pi.single s 1) q = if s = Fin.rev q then -1 else 0 := by
  by_cases h : s = Fin.rev q
  · subst h; simp [reflHom]
  · have h' : Fin.rev q ≠ s := fun e => h e.symm
    simp [reflHom, Pi.single_apply, h, h']

lemma pair_count (N : ℕ) (a : Fin N → ℤ) (r : Fin N) (ha : ∀ s, a s = if s = r then -1 else 0) :
    (∑ t : Fin N, ∑ s : Fin N, if s < t then a s + a t else 0) = -((N : ℤ) - 1) := by
  have h1 : (∑ t : Fin N, ∑ s : Fin N, if s < t then a s + a t else 0)
      = ∑ t : Fin N, ∑ s : Fin N, ((if s < t then a s else 0) + (if s < t then a t else 0)) := by
    refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  have h2 : (∑ t : Fin N, ∑ s : Fin N, (if s < t then a t else 0))
      = ∑ t : Fin N, ∑ s : Fin N, (if t < s then a s else 0) := sum_comm
  have h3 : ∀ t : Fin N, (∑ s : Fin N, ((if s < t then a s else 0) + (if t < s then a s else 0)))
      = (∑ s : Fin N, a s) - a t := by
    intro t
    have : ∀ s : Fin N, ((if s < t then a s else 0) + (if t < s then a s else 0))
        = a s - (if s = t then a s else 0) := by
      intro s
      rcases lt_trichotomy s t with h | h | h
      · simp [h, ne_of_lt h, not_lt_of_gt h]
      · simp [h]
      · simp [h, ne_of_gt h, not_lt_of_gt h]
    rw [sum_congr rfl fun s _ => this s, sum_sub_distrib, sum_ite_eq' univ t a]
    simp
  have hA : (∑ s : Fin N, a s) = -1 := by
    rw [sum_congr rfl fun s _ => ha s, sum_ite_eq']; simp
  rw [h1, sum_congr rfl fun t _ => sum_add_distrib, sum_add_distrib, h2, ← sum_add_distrib,
    sum_congr rfl fun t _ => (sum_add_distrib).symm, sum_congr rfl fun t _ => h3 t, hA,
    sum_sub_distrib, sum_congr rfl fun s _ => ha s, sum_ite_eq']
  simp; ring

lemma refl_prod (N : ℕ) :
    (∏ t : Fin N, ∏ s : Fin N, if s < t then (1 - Zr N s + Zr N s * Zr N t) else 1)
      = AddMonoidAlgebra.single (fun _ => -((N : ℤ) - 1)) 1 * Q2 N := by
  have e1 : ∀ s t : Fin N, (if s < t then (1 - Zr N s + Zr N s * Zr N t) else (1 : Alg N))
      = AddMonoidAlgebra.single (if s < t then reflHom N (Pi.single s 1) + reflHom N (Pi.single t 1)
          else 0) 1 * (if s < t then T (Fin.rev t) (Fin.rev s) else 1) := by
    intro s t
    split_ifs
    · rw [refl_factor]; unfold Zr; rw [AddMonoidAlgebra.single_mul_single, one_mul]
    · rw [mul_one]; rfl
  simp only [e1, prod_mul_distrib, AddMonoidAlgebra.prod_single, prod_const_one]
  congr 1
  · congr 1
    funext q
    simp only [Finset.sum_apply]
    have := pair_count N (fun s => reflHom N (Pi.single s 1) q) (Fin.rev q)
      (fun s => refl_single_apply N s q)
    rw [← this]
    refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  · rw [prod_comm, ← Equiv.prod_comp Fin.revPerm]
    unfold Q2
    refine prod_congr rfl fun t _ => ?_
    rw [← Equiv.prod_comp Fin.revPerm]
    refine prod_congr rfl fun s _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.rev_lt_rev]

/-- **Reflection symmetry**: `α(N; −k_N, …, −k_1) = α(N; k_1, …, k_N)`. -/
theorem alpha_refl (N : ℕ) (k : Fin N → ℤ) : alpha N (reflHom N k) = alpha N k := by
  have hrel : Rel (reflHom N)
      (∏ t : Fin N, ∏ s : Fin N, if s < t then (1 - Zr N s + Zr N s * Zr N t) else 1) (Q2 N) :=
    Rel.prod univ _ _ fun t _ => Rel.prod univ _ _ fun s _ => Rel.ite (s < t)
      ((Rel.one.sub (Rel.single _ _ _ rfl)).add ((Rel.single _ _ _ rfl).mul (Rel.single _ _ _ rfl)))
  have h := hrel (Pi' N) k
  rw [show (fun m => Pi' N (reflHom N m)) = Pi' N from funext (Pi'_refl N), refl_prod,
    act_mul_apply, act_single, one_mul, ← alpha_eq_Q2, ← alpha_eq_Q2, alpha_translate] at h
  exact h.symm

/-- Reflection combined with a translation: `α(N; c − k_N, …, c − k_1) = α(N; k)`. -/
theorem alpha_refl_shift (N : ℕ) (k : Fin N → ℤ) (c : ℤ) :
    alpha N (fun p => c - k (Fin.rev p)) = alpha N k := by
  have : (fun p => c - k (Fin.rev p)) = reflHom N k + fun _ => c := by
    funext p; simp [reflHom]; ring
  rw [this, alpha_translate, alpha_refl]

end MT
```

### `MTWin.lean`

```lean
import MTWindow
import MTCertW1
import MTCertW3

/-!
# The window identities W1–W4 at arbitrary positions and contexts
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace MT

open Finset

theorem Q2_two : Q2 2 = prodT pairs2 := by
  simp only [Q2, Fin.prod_univ_two, prodT, pairs2, ← Tn_eq]
  norm_num

theorem Q2_three : Q2 3 = prodT pairs3 := by
  simp only [Q2, Fin.prod_univ_three, prodT, pairs3, ← Tn_eq]
  norm_num

theorem Q2_four : Q2 4 = prodT pairs4 := by
  simp only [Q2, Fin.prod_univ_four, prodT, pairs4, ← Tn_eq]
  norm_num
  ring

variable {N w : ℕ}

lemma eq_ins (s0 : ℕ) (hw : s0 + w ≤ N) (k r : Fin N → ℤ) (y : Fin w → ℤ)
    (hout : ∀ p : Fin N, ¬ inW s0 w p → r p = k p)
    (hin : ∀ i : Fin w, r (wpos s0 hw i) = y i) : r = ins s0 k y := by
  funext p
  unfold ins
  split_ifs with h
  · have := hin ⟨p - s0, by omega⟩
    rw [← this]
    congr 1
    simp only [wpos, Fin.ext_iff]; omega
  · exact hout p h

/-- W1 in row form. -/
theorem W1 (s0 : ℕ) (hw : s0 + 4 ≤ N) (a : ℤ) (k r1 r2 r3 : Fin N → ℤ)
    (o1 : ∀ p, ¬ inW s0 4 p → r1 p = k p) (o2 : ∀ p, ¬ inW s0 4 p → r2 p = k p)
    (o3 : ∀ p, ¬ inW s0 4 p → r3 p = k p)
    (i1 : ∀ i, r1 (wpos s0 hw i) = vec [64, 66, 65, 66] i + a)
    (i2 : ∀ i, r2 (wpos s0 hw i) = vec [65, 64, 65, 66] i + a)
    (i3 : ∀ i, r3 (wpos s0 hw i) = vec [64, 64, 65, 66] i + a) :
    alpha N r1 - alpha N r2 - alpha N r3 = 0 := by
  have h := window_identity s0 hw pairs4 Q2_four certW1
    (fun h hh => cert_sound _ _ _ _ checkW1 h hh) k a
  rw [eq_ins s0 hw k r1 ((vec [64, 66, 65, 66] : Fin 4 → ℤ) + fun _ => a) o1 i1, eq_ins s0 hw k r2 ((vec [65, 64, 65, 66] : Fin 4 → ℤ) + fun _ => a) o2 i2, eq_ins s0 hw k r3 ((vec [64, 64, 65, 66] : Fin 4 → ℤ) + fun _ => a) o3 i3]
  simp only [certW1, mk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
  push_cast at h
  linarith

/-- W2 in row form. -/
theorem W2 (s0 : ℕ) (hw : s0 + 3 ≤ N) (a : ℤ) (k r1 r2 : Fin N → ℤ)
    (o1 : ∀ p, ¬ inW s0 3 p → r1 p = k p) (o2 : ∀ p, ¬ inW s0 3 p → r2 p = k p)
    (i1 : ∀ i, r1 (wpos s0 hw i) = vec [64, 64, 65] i + a)
    (i2 : ∀ i, r2 (wpos s0 hw i) = vec [64, 65, 65] i + a) :
    alpha N r1 = alpha N r2 := by
  have h := window_identity s0 hw pairs3 Q2_three certW2
    (fun h hh => cert_sound _ _ _ _ checkW2 h hh) k a
  rw [eq_ins s0 hw k r1 ((vec [64, 64, 65] : Fin 3 → ℤ) + fun _ => a) o1 i1, eq_ins s0 hw k r2 ((vec [64, 65, 65] : Fin 3 → ℤ) + fun _ => a) o2 i2]
  simp only [certW2, mk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
  push_cast at h
  linarith

/-- W3 in row form. -/
theorem W3 (s0 : ℕ) (hw : s0 + 4 ≤ N) (a : ℤ) (k r1 r2 : Fin N → ℤ)
    (o1 : ∀ p, ¬ inW s0 4 p → r1 p = k p) (o2 : ∀ p, ¬ inW s0 4 p → r2 p = k p)
    (i1 : ∀ i, r1 (wpos s0 hw i) = vec [64, 64, 66, 66] i + a)
    (i2 : ∀ i, r2 (wpos s0 hw i) = vec [64, 64, 65, 66] i + a) :
    alpha N r1 = alpha N r2 := by
  have h := window_identity s0 hw pairs4 Q2_four certW3
    (fun h hh => cert_sound _ _ _ _ checkW3 h hh) k a
  rw [eq_ins s0 hw k r1 ((vec [64, 64, 66, 66] : Fin 4 → ℤ) + fun _ => a) o1 i1, eq_ins s0 hw k r2 ((vec [64, 64, 65, 66] : Fin 4 → ℤ) + fun _ => a) o2 i2]
  simp only [certW3, mk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
  push_cast at h
  linarith

/-- W4 in row form: `W(a+1,a)+W(a,a−1)−W(a,a)+W(a−1,a)+W(a,a+1)−W(a−1,a+1) = 0`. -/
theorem W4 (s0 : ℕ) (hw : s0 + 2 ≤ N) (a : ℤ) (k r1 r2 r3 r4 r5 r6 : Fin N → ℤ)
    (o1 : ∀ p, ¬ inW s0 2 p → r1 p = k p) (o2 : ∀ p, ¬ inW s0 2 p → r2 p = k p)
    (o3 : ∀ p, ¬ inW s0 2 p → r3 p = k p) (o4 : ∀ p, ¬ inW s0 2 p → r4 p = k p)
    (o5 : ∀ p, ¬ inW s0 2 p → r5 p = k p) (o6 : ∀ p, ¬ inW s0 2 p → r6 p = k p)
    (i1 : ∀ i, r1 (wpos s0 hw i) = vec [65, 64] i + a)
    (i2 : ∀ i, r2 (wpos s0 hw i) = vec [64, 63] i + a)
    (i3 : ∀ i, r3 (wpos s0 hw i) = vec [64, 64] i + a)
    (i4 : ∀ i, r4 (wpos s0 hw i) = vec [63, 64] i + a)
    (i5 : ∀ i, r5 (wpos s0 hw i) = vec [64, 65] i + a)
    (i6 : ∀ i, r6 (wpos s0 hw i) = vec [63, 65] i + a) :
    alpha N r1 + alpha N r2 - alpha N r3 + alpha N r4 + alpha N r5 - alpha N r6 = 0 := by
  have h := window_identity s0 hw pairs2 Q2_two certW4
    (fun h hh => cert_sound _ _ _ _ checkW4 h hh) k a
  rw [eq_ins s0 hw k r1 ((vec [65, 64] : Fin 2 → ℤ) + fun _ => a) o1 i1, eq_ins s0 hw k r2 ((vec [64, 63] : Fin 2 → ℤ) + fun _ => a) o2 i2, eq_ins s0 hw k r3 ((vec [64, 64] : Fin 2 → ℤ) + fun _ => a) o3 i3,
    eq_ins s0 hw k r4 ((vec [63, 64] : Fin 2 → ℤ) + fun _ => a) o4 i4, eq_ins s0 hw k r5 ((vec [64, 65] : Fin 2 → ℤ) + fun _ => a) o5 i5, eq_ins s0 hw k r6 ((vec [63, 65] : Fin 2 → ℤ) + fun _ => a) o6 i6]
  simp only [certW4, mk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
  push_cast at h
  linarith

end MT
```

### `MTRowsDef.lean`

```lean
import MTRows
import MTSym
import MTWin

/-!
# The rows of Riegler's Conjecture 6 and the auxiliary rows of the proof
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace MT

open Finset

/-- Riegler's row `(1, 2, …, i−1, i+1, i, i+1, …, n)` (length `n+1`; 0-based position `p` holds
`p+1` if `p+1 < i`, `i+1` if `p+1 = i`, and `p` if `p+1 > i`). -/
def bRow (n i : ℕ) : Fin (n + 1) → ℤ :=
  fun p => if (p : ℕ) + 1 < i then (p : ℤ) + 1 else if (p : ℕ) + 1 = i then (i : ℤ) + 1 else (p : ℤ)

/-- The row `(1, …, j−1, j+1, …, n) = [n] ∖ {j}` (length `n−1`). -/
def rowMinus (n j : ℕ) : Fin (n - 1) → ℤ :=
  fun p => if (p : ℕ) + 1 < j then (p : ℤ) + 1 else (p : ℤ) + 2

/-- `A_{n,j} = α(n−1; 1, …, j−1, j+1, …, n)` (the source's identification of the refined ASM
number with a value of the monotone-triangle polynomial). -/
noncomputable def A (n j : ℕ) : ℚ := alpha (n - 1) (rowMinus n j)

/-- `(1, …, m, m, m+1, …, n)` (length `n+1`, the value `m` doubled). -/
def dupRow (n m : ℕ) : Fin (n + 1) → ℤ := fun p => if (p : ℕ) < m then (p : ℤ) + 1 else (p : ℤ)

/-- `(1, …, i−1, i, i−1, i+1, …, n)`. -/
def cRow (n i : ℕ) : Fin (n + 1) → ℤ := fun p =>
  if (p : ℕ) + 1 < i then (p : ℤ) + 1 else if (p : ℕ) + 1 = i then (i : ℤ)
  else if (p : ℕ) = i then (i : ℤ) - 1 else (p : ℤ)

/-- `(1, …, i−1, i−1, i+1, i+1, i+2, …, n)`. -/
def ddRow (n i : ℕ) : Fin (n + 1) → ℤ := fun p =>
  if (p : ℕ) + 1 < i then (p : ℤ) + 1 else if (p : ℕ) + 1 = i then (i : ℤ) - 1
  else if (p : ℕ) = i then (i : ℤ) + 1 else (p : ℤ)

macro "out_tac" : tactic => `(tactic| (
  intro p hp
  simp only [inW, not_and_or, not_le, not_lt] at hp
  simp only [bRow, dupRow, cRow, ddRow]
  split_ifs <;> omega))

macro "in_tac" : tactic => `(tactic| (
  intro q
  fin_cases q <;> simp [wpos, vec, bRow, dupRow, cRow, ddRow] <;> (try split_ifs) <;> omega))

/-- Step 1: the duplicate rows all have the same value. -/
theorem dup_step (n m : ℕ) (hm1 : 1 ≤ m) (hm2 : m + 1 ≤ n) :
    alpha (n + 1) (dupRow n m) = alpha (n + 1) (dupRow n (m + 1)) :=
  W2 (m - 1) (by omega) (m : ℤ) (dupRow n m) (dupRow n m) (dupRow n (m + 1))
    (by intro p _; rfl) (by out_tac) (by in_tac) (by in_tac)

theorem dup_top (n : ℕ) : alpha (n + 2) (dupRow (n + 1) (n + 1)) = alpha (n + 1) (ap (n + 1) 1) := by
  rw [← alpha_apdup n 1]
  congr 1
  funext p
  induction p using Fin.lastCases with
  | last =>
    simp only [dupRow, Fin.snoc_last, Fin.val_last]
    split_ifs <;> push_cast <;> omega
  | cast p =>
    have := p.isLt
    simp only [dupRow, Fin.snoc_castSucc, ap, Fin.coe_castSucc]
    split_ifs <;> push_cast <;> omega

theorem dup_val (n m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ n + 1) :
    alpha (n + 2) (dupRow (n + 1) m) = alpha (n + 1) (ap (n + 1) 1) := by
  have key : ∀ d, d ≤ n → alpha (n + 2) (dupRow (n + 1) (n + 1 - d)) = alpha (n + 1) (ap (n + 1) 1) := by
    intro d
    induction d with
    | zero => intro _; simpa using dup_top n
    | succ d ih =>
      intro hd
      rw [dup_step (n + 1) (n + 1 - (d + 1)) (by omega) (by omega),
        show n + 1 - (d + 1) + 1 = n + 1 - d by omega]
      exact ih (by omega)
  have := key (n + 1 - m) (by omega)
  rwa [show n + 1 - (n + 1 - m) = m by omega] at this

/-- Step 2 (W1): `α(b_{i+1}) = α(b_i) + α(dup_i)`. -/
theorem b_step (n i : ℕ) (hi1 : 1 ≤ i) (hi2 : i + 2 ≤ n) :
    alpha (n + 1) (bRow n (i + 1)) = alpha (n + 1) (bRow n i) + alpha (n + 1) (dupRow n i) := by
  have h := W1 (i - 1) (by omega) (i : ℤ) (bRow n i) (bRow n (i + 1)) (bRow n i) (dupRow n i)
    (by out_tac) (by intro p _; rfl) (by out_tac) (by in_tac) (by in_tac) (by in_tac)
  linarith

/-- Route B (W4 and W3): `α(b_i) = −α(c_i)` for `2 ≤ i ≤ n−1`. -/
theorem b_neg_c (n i : ℕ) (hi1 : 2 ≤ i) (hi2 : i + 1 ≤ n) :
    alpha (n + 1) (bRow n i) = - alpha (n + 1) (cRow n i) := by
  have h4 := W4 (i - 1) (by omega) (i : ℤ) (bRow n i) (bRow n i) (cRow n i) (dupRow n i)
    (dupRow n (i - 1)) (dupRow n (i + 1)) (ddRow n i)
    (by intro p _; rfl) (by out_tac) (by out_tac) (by out_tac) (by out_tac) (by out_tac)
    (by in_tac) (by in_tac) (by in_tac) (by in_tac) (by in_tac) (by in_tac)
  have h3 := W3 (i - 2) (by omega) ((i : ℤ) - 1) (ddRow n i) (ddRow n i) (dupRow n (i - 1))
    (by intro p _; rfl) (by out_tac) (by in_tac) (by in_tac)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have d1 := dup_val n' i (by omega) (by omega)
  have d2 := dup_val n' (i - 1) (by omega) (by omega)
  have d3 := dup_val n' (i + 1) (by omega) (by omega)
  linarith

/-- Reflection: `α(c_i) = α(b_{n+1−i})`. -/
theorem c_refl (n i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    alpha (n + 1) (cRow n i) = alpha (n + 1) (bRow n (n + 1 - i)) := by
  rw [← alpha_refl_shift (n + 1) (bRow n (n + 1 - i)) ((n : ℤ) + 1)]
  congr 1
  funext p
  have hp := p.isLt
  simp only [bRow, cRow, Fin.val_rev]
  split_ifs <;> push_cast at * <;> omega

/-- `∑_{j=1}^{n} A_{n,j} = α(n; 1, …, n)`. -/
theorem sum_A (m : ℕ) :
    ∑ j ∈ Icc 1 (m + 1), A (m + 1) j = alpha (m + 1) (ap (m + 1) 1) := by
  rw [alpha_ap m 1]
  have hre : ∀ r : Fin (m + 1), A (m + 1) ((r : ℕ) + 1) = alpha m (fun i => ap (m + 1) 1 (r.succAbove i)) := by
    intro r
    unfold A
    show alpha m (rowMinus (m + 1) ((r : ℕ) + 1)) = _
    congr 1
    funext p
    simp only [rowMinus, ap, Fin.succAbove]
    split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_iff_val_lt_val] <;> omega
  rw [← sum_congr rfl fun r _ => hre r]
  rw [Fin.sum_univ_eq_sum_range (fun x => A (m + 1) (x + 1)) (m + 1)]
  refine Finset.sum_nbij' (fun j => j - 1) (fun x => x + 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_Icc] at hj; simp only [mem_range]; omega
  · intro x hx; simp only [mem_range] at hx; simp only [mem_Icc]; omega
  · intro j hj; simp only [mem_Icc] at hj; omega
  · intro x _; omega
  · intro j hj; simp only [mem_Icc] at hj; congr 1; omega

/-- Symmetry `A_{n,j} = A_{n,n+1−j}`. -/
theorem A_symm (m j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ m + 1) : A (m + 1) j = A (m + 1) (m + 2 - j) := by
  unfold A
  show alpha m (rowMinus (m + 1) j) = alpha m (rowMinus (m + 1) (m + 2 - j))
  rw [← alpha_refl_shift m (rowMinus (m + 1) (m + 2 - j)) ((m : ℤ) + 2)]
  congr 1
  funext p
  have hp := p.isLt
  simp only [rowMinus, Fin.val_rev]
  split_ifs <;> push_cast at * <;> omega

theorem sum_jA (m : ℕ) :
    2 * ∑ j ∈ Icc 1 (m + 1), (j : ℚ) * A (m + 1) j
      = ((m : ℚ) + 2) * ∑ j ∈ Icc 1 (m + 1), A (m + 1) j := by
  have hr : ∑ j ∈ Icc 1 (m + 1), (j : ℚ) * A (m + 1) j
      = ∑ j ∈ Icc 1 (m + 1), ((m : ℚ) + 2 - j) * A (m + 1) j := by
    refine Finset.sum_nbij' (fun j => m + 2 - j) (fun j => m + 2 - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Icc] at *; omega
    · intro j hj; simp only [mem_Icc] at *; omega
    · intro j hj; simp only [mem_Icc] at hj; omega
    · intro j hj; simp only [mem_Icc] at hj; omega
    · intro j hj
      simp only [mem_Icc] at hj
      rw [A_symm m j hj.1 hj.2, Nat.cast_sub (by omega)]
      push_cast; ring
  have : 2 * ∑ j ∈ Icc 1 (m + 1), (j : ℚ) * A (m + 1) j
      = ∑ j ∈ Icc 1 (m + 1), (j : ℚ) * A (m + 1) j
        + ∑ j ∈ Icc 1 (m + 1), ((m : ℚ) + 2 - j) * A (m + 1) j := by rw [← hr]; ring
  rw [this, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

end MT
```

### `MTMain.lean`

```lean
import MTRowsDef

/-!
# Riegler's Conjecture 6 (arXiv:1207.4437, eq. (4.12); FPSAC 2013, Conjecture 5)

For `n ≥ 1` and `1 ≤ i ≤ n − 1`:
`α(n+1; 1, …, i−1, i+1, i, i+1, …, n) = −∑_{j=1}^{n} (j − i) A_{n,j}`,
where `α` is the monotone-triangle polynomial given by Fischer's operator formula and
`A_{n,j} = α(n−1; 1, …, j−1, j+1, …, n)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace MT

open Finset

lemma alpha_zero (k : Fin 0 → ℤ) : alpha 0 k = 1 := by
  rw [alpha_eq_Q2]; simp [Q2, Pi', act_one_apply]

lemma alpha_one (k : Fin 1 → ℤ) : alpha 1 k = 1 := by
  rw [alpha_rec]; simp [S, alpha_zero]

lemma ssum_self (a : ℤ) (g : ℤ → ℚ) : ssum a a g = g a := by
  unfold ssum
  have h1 : Ico a (a + 1) = {a} := by ext x; simp only [mem_Ico, mem_singleton]; omega
  rw [h1, Ico_eq_empty_of_le (by omega), sum_singleton, sum_empty, sub_zero]

lemma ssum_pred (a : ℤ) (g : ℤ → ℚ) : ssum (a + 1) a g = 0 := by
  unfold ssum; simp

lemma alpha_two (l : Fin 2 → ℤ) : alpha 2 l = ssum (l 0) (l 1) (fun _ => 1) := by
  rw [alpha_rec]; simp [S, alpha_one]

/-- The case `n = 2`: `α(3; 2, 1, 2) = −1`. -/
theorem case_n2 : alpha 3 (bRow 2 1) = -1 := by
  rw [alpha_rec]
  simp only [S]
  have e1 : bRow 2 1 (Fin.last 1).castSucc = 1 := by decide
  have e2 : bRow 2 1 (Fin.last 2) = 2 := by decide
  have e3 : Fin.init (bRow 2 1) 0 = 2 := by decide
  have e4 : Fin.init (bRow 2 1) 1 = 1 := by decide
  rw [e1, e2, e3, e4]
  have hz : ∀ l : ℤ, ssum 2 1 (fun x => alpha 2 (Fin.snoc (fun _ : Fin 1 => x) l : Fin 2 → ℤ)) = 0 :=
    fun l => by simpa using ssum_pred 1 (fun x => alpha 2 (Fin.snoc (fun _ : Fin 1 => x) l))
  simp only [hz]
  rw [alpha_two]
  have : ssum 1 2 (fun _ : ℤ => (0 : ℚ)) = 0 := by unfold ssum; simp
  rw [this]
  simp [Fin.snoc, ssum_self]

/-- **Riegler's Conjecture 6** (eq. (4.12) of arXiv:1207.4437), for every `n` and every
`1 ≤ i ≤ n − 1`, with `α` given by Fischer's operator formula `MT.alpha` and
`A_{n,j} = α(n−1; [n] ∖ {j})`. -/
theorem riegler_conjecture6 (n i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ n - 1) :
    alpha (n + 1) (bRow n i) = - ∑ j ∈ Icc 1 n, ((j : ℚ) - i) * A n j := by
  have hn : 2 ≤ n := by omega
  rcases Nat.eq_or_lt_of_le hn with h2 | h3
  · subst h2
    have hi : i = 1 := by omega
    subst hi
    rw [case_n2]
    have hA : ∀ j, A 2 j = 1 := fun j => alpha_one _
    rw [show Icc 1 2 = {1, 2} from by decide, sum_pair (by decide)]
    simp [hA]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    set An := alpha (m + 1) (ap (m + 1) 1) with hAn
    have dv : ∀ k, 1 ≤ k → k ≤ m + 1 → alpha (m + 2) (dupRow (m + 1) k) = An :=
      fun k h1 h2 => dup_val m k h1 h2
    have lin : ∀ k, 1 ≤ k → k ≤ m →
        alpha (m + 2) (bRow (m + 1) k) = alpha (m + 2) (bRow (m + 1) 1) + ((k : ℚ) - 1) * An := by
      intro k hk1
      induction k, hk1 using Nat.le_induction with
      | base => intro _; simp
      | succ k hk ih =>
        intro hk2
        rw [b_step (m + 1) k hk (by omega), ih (by omega), dv k hk (by omega)]
        push_cast; ring
    have hb2 : alpha (m + 2) (bRow (m + 1) 2) = - alpha (m + 2) (bRow (m + 1) m) := by
      rw [b_neg_c (m + 1) 2 (le_refl 2) (by omega), c_refl (m + 1) 2 (by omega) (by omega),
        show m + 1 + 1 - 2 = m by omega]
    have l2 := lin 2 (by omega) (by omega)
    have lm := lin m (by omega) (le_refl m)
    have li := lin i hi1 (by omega)
    have hSA := sum_A m
    have hSJ := sum_jA m
    have hsplit : ∑ j ∈ Icc 1 (m + 1), ((j : ℚ) - i) * A (m + 1) j
        = ∑ j ∈ Icc 1 (m + 1), (j : ℚ) * A (m + 1) j - (i : ℚ) * ∑ j ∈ Icc 1 (m + 1), A (m + 1) j := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      ring
    show alpha (m + 2) (bRow (m + 1) i) = _
    rw [hsplit, li]
    rw [← hAn] at hSA
    push_cast at l2 lm
    linear_combination (1 / 2 : ℚ) * hb2 - (1 / 2 : ℚ) * l2 - (1 / 2 : ℚ) * lm
      + (1 / 2 : ℚ) * hSJ + (((m : ℚ) + 2) / 2 - i) * hSA

end MT
```

### `MTFischer.lean`

```lean
import MTMain
import Mathlib.Data.Fintype.Pi

/-!
# The operator formula counts monotone triangles at strictly increasing rows

`mtNum n k` is the number of monotone triangles with bottom row `k`, computed by the defining
decomposition "penultimate row `l` + monotone triangle with bottom row `l`": `l` ranges over the
strictly increasing rows with `k_i ≤ l_i ≤ k_{i+1}` (this is exactly the condition
`a_{i+1,j} ≤ a_{i,j} ≤ a_{i+1,j+1}`, `a_{i,j} < a_{i,j+1}` of the source between the last two
rows).  We prove `alpha n k = mtNum n k` for every strictly increasing `k` (one direction of
Fischer's theorem), and hence `A_{n,j}` is the number of monotone triangles with bottom row
`(1, …, j−1, j+1, …, n)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace MT

open Finset

/-- Strictly increasing rows `l` with `k_i ≤ l_i ≤ k_{i+1}`. -/
def interlace (n : ℕ) (k : Fin (n + 1) → ℤ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i : Fin n => Icc (k i.castSucc) (k i.succ)).filter
    (fun l => ∀ i j : Fin n, i < j → l i < l j)

/-- Number of monotone triangles with bottom row `k`. -/
def mtNum : (n : ℕ) → (Fin n → ℤ) → ℕ
  | 0, _ => 1
  | n + 1, k => ∑ l ∈ interlace n k, mtNum n l

lemma mem_interlace {n : ℕ} {k : Fin (n + 1) → ℤ} {l : Fin n → ℤ} :
    l ∈ interlace n k ↔ (∀ i, k i.castSucc ≤ l i ∧ l i ≤ k i.succ) ∧ StrictMono l := by
  simp only [interlace, mem_filter, Fintype.mem_piFinset, mem_Icc]
  rfl

lemma strictMono_snoc_iff {n : ℕ} (m : Fin n → ℤ) (x : ℤ) :
    StrictMono (Fin.snoc m x : Fin (n + 1) → ℤ) ↔ StrictMono m ∧ ∀ i, m i < x := by
  constructor
  · intro h
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · have := h (Fin.castSucc_lt_castSucc_iff.mpr hab)
      simpa using this
    · have := h (Fin.castSucc_lt_last i)
      simpa using this
  · rintro ⟨h1, h2⟩ a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast a => simpa using h2 a
    | cast b =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (not_lt.mpr (Fin.le_last _))
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact h1 (Fin.castSucc_lt_castSucc_iff.mp hab)

lemma strictMono_init {n : ℕ} {l : Fin (n + 1) → ℤ} (h : StrictMono l) : StrictMono (Fin.init l) :=
  fun a b hab => h (Fin.castSucc_lt_castSucc_iff.mpr hab)

lemma ssum_le (a b : ℤ) (hab : a ≤ b + 1) (g : ℤ → ℚ) : ssum a b g = ∑ x ∈ Icc a b, g x := by
  unfold ssum
  rw [Ico_eq_empty_of_le hab, sum_empty, sub_zero,
    show Ico a (b + 1) = Icc a b from by ext x; simp only [mem_Ico, mem_Icc]; omega]

lemma bound_init {n : ℕ} {k : Fin (n + 2) → ℤ} {l : Fin (n + 1) → ℤ}
    (h : ∀ i, k i.castSucc ≤ l i ∧ l i ≤ k i.succ) :
    ∀ i : Fin n, Fin.init k i.castSucc ≤ Fin.init l i ∧ Fin.init l i ≤ Fin.init k i.succ := by
  intro i
  have h1 := h i.castSucc
  rw [Fin.succ_castSucc] at h1
  exact h1

lemma bound_snoc {n : ℕ} {k : Fin (n + 2) → ℤ} {m : Fin n → ℤ} {x : ℤ}
    (hm : ∀ i : Fin n, Fin.init k i.castSucc ≤ m i ∧ m i ≤ Fin.init k i.succ)
    (hx : k (Fin.last n).castSucc ≤ x ∧ x ≤ k (Fin.last (n + 1))) :
    ∀ i : Fin (n + 1), k i.castSucc ≤ (Fin.snoc m x : Fin (n + 1) → ℤ) i ∧
      (Fin.snoc m x : Fin (n + 1) → ℤ) i ≤ k i.succ := by
  intro i
  induction i using Fin.lastCases with
  | last => rw [Fin.snoc_last, Fin.succ_last]; exact hx
  | cast i =>
    rw [Fin.snoc_castSucc, Fin.succ_castSucc]
    exact hm i

/-- On strictly increasing rows the summation operator is the sum over strictly increasing
interlacing rows (Riegler (2.1)). -/
theorem S_strict : ∀ (n : ℕ) (k : Fin (n + 1) → ℤ), StrictMono k → ∀ A : (Fin n → ℤ) → ℚ,
    S n k A = ∑ l ∈ interlace n k, A l
  | 0, k, hk, A => by
    have : interlace 0 k = {Fin.elim0} := by
      ext l
      simp only [mem_interlace, mem_singleton]
      constructor
      · intro _; funext i; exact i.elim0
      · intro _; exact ⟨fun i => i.elim0, fun a => a.elim0⟩
    rw [this, sum_singleton]; rfl
  | 1, k, hk, A => by
    simp only [S]
    rw [ssum_le _ _ (by have := hk (show (0 : Fin 2) < 1 by decide); omega)]
    refine Finset.sum_nbij' (fun x => fun _ => x) (fun l => l 0) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_Icc] at hx
      rw [mem_interlace]
      refine ⟨fun i => ?_, fun a b hab => ?_⟩
      · rw [Fin.fin_one_eq_zero i]; exact hx
      · exact absurd hab (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; exact lt_irrefl _)
    · intro l hl
      rw [mem_interlace] at hl
      simpa using hl.1 0
    · intro x _; rfl
    · intro l _; funext i; rw [Fin.fin_one_eq_zero i]
    · intro x _; rfl
  | n + 2, k, hk, A => by
    simp only [S]
    set c := k (Fin.last (n + 1)).castSucc with hc
    set d := k (Fin.last (n + 2)) with hd
    have hcd : c < d := hk (Fin.castSucc_lt_last _)
    have hik : StrictMono (Fin.init k) := strictMono_init hk
    have hiik : StrictMono (Fin.init (Fin.init k)) := strictMono_init hik
    rw [ssum_le _ _ (by omega)]
    simp only [S_strict (n + 1) (Fin.init k) hik, S_strict n (Fin.init (Fin.init k)) hiik]
    rw [sum_comm, ← sum_product' (f := fun m x => A (Fin.snoc m x : Fin (n + 2) → ℤ))]
    rw [← sum_filter_add_sum_filter_not (interlace (n + 1) (Fin.init k) ×ˢ Icc c d)
      (fun p => p.1 (Fin.last n) < p.2)]
    -- facts about a pair in the product
    have hpair : ∀ p ∈ interlace (n + 1) (Fin.init k) ×ˢ Icc c d,
        p.1 (Fin.last n) ≤ c ∧ c ≤ p.2 ∧ p.2 ≤ d := by
      intro p hp
      rw [mem_product, mem_interlace, mem_Icc] at hp
      exact ⟨(hp.1.1 (Fin.last n)).2, hp.2.1, hp.2.2⟩
    have hbad : ∑ p ∈ (interlace (n + 1) (Fin.init k) ×ˢ Icc c d).filter
          (fun p => ¬ p.1 (Fin.last n) < p.2),
        A (Fin.snoc p.1 p.2 : Fin (n + 2) → ℤ)
        = ∑ m ∈ interlace n (Fin.init (Fin.init k)),
          A (Fin.snoc (Fin.snoc m c : Fin (n + 1) → ℤ) c : Fin (n + 2) → ℤ) := by
      refine Finset.sum_nbij' (fun p => Fin.init p.1)
        (fun m => ((Fin.snoc m c : Fin (n + 1) → ℤ), c)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        rw [mem_filter] at hp
        have hp1 := hp.1
        rw [mem_product, mem_interlace] at hp1
        rw [mem_interlace]
        exact ⟨bound_init hp1.1.1, strictMono_init hp1.1.2⟩
      · intro m hm
        rw [mem_interlace] at hm
        rw [mem_filter, mem_product, mem_interlace, mem_Icc, strictMono_snoc_iff]
        dsimp only
        rw [Fin.snoc_last]
        refine ⟨⟨⟨bound_snoc hm.1 ⟨?_, le_refl c⟩, hm.2, fun i => ?_⟩, le_refl c, hcd.le⟩,
          lt_irrefl c⟩
        · exact (hk (Fin.castSucc_lt_castSucc_iff.mpr (Fin.castSucc_lt_last _))).le
        · have h1 := (hm.1 i).2
          have h2 : Fin.init (Fin.init k) i.succ < c := by
            show k (i.succ.castSucc.castSucc) < k (Fin.last (n + 1)).castSucc
            apply hk
            rw [Fin.lt_iff_val_lt_val]
            simp
          exact lt_of_le_of_lt h1 h2
      · intro p hp
        rw [mem_filter] at hp
        obtain ⟨h1, h2, h3⟩ := hpair p hp.1
        have h4 := not_lt.mp hp.2
        have hx : p.2 = c := by omega
        have hl : p.1 (Fin.last n) = c := by omega
        show ((Fin.snoc (Fin.init p.1) c : Fin (n + 1) → ℤ), c) = p
        rw [← hl, Fin.snoc_init_self, hl, ← hx]
      · intro m _
        show Fin.init (Fin.snoc m c : Fin (n + 1) → ℤ) = m
        rw [Fin.init_snoc]
      · intro p hp
        rw [mem_filter] at hp
        obtain ⟨h1, h2, h3⟩ := hpair p hp.1
        have h4 := not_lt.mp hp.2
        have hx : p.2 = c := by omega
        have hl : p.1 (Fin.last n) = c := by omega
        show A (Fin.snoc p.1 p.2 : Fin (n + 2) → ℤ)
          = A (Fin.snoc (Fin.snoc (Fin.init p.1) c : Fin (n + 1) → ℤ) c : Fin (n + 2) → ℤ)
        rw [hx, ← hl, Fin.snoc_init_self]
    have hgood : ∑ p ∈ (interlace (n + 1) (Fin.init k) ×ˢ Icc c d).filter
          (fun p => p.1 (Fin.last n) < p.2),
        A (Fin.snoc p.1 p.2 : Fin (n + 2) → ℤ) = ∑ l ∈ interlace (n + 2) k, A l := by
      refine Finset.sum_nbij' (fun p => (Fin.snoc p.1 p.2 : Fin (n + 2) → ℤ))
        (fun l => (Fin.init l, l (Fin.last _))) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        rw [mem_filter] at hp
        have hpp := hpair p hp.1
        have hp1 := hp.1
        rw [mem_product, mem_interlace] at hp1
        rw [mem_interlace, strictMono_snoc_iff]
        refine ⟨bound_snoc hp1.1.1 ⟨hpp.2.1, hpp.2.2⟩, hp1.1.2, fun i => ?_⟩
        rcases (Fin.le_last i).lt_or_eq with h | h
        · exact lt_trans (hp1.1.2 h) hp.2
        · rw [h]; exact hp.2
      · intro l hl
        rw [mem_interlace] at hl
        rw [mem_filter, mem_product, mem_interlace, mem_Icc]
        refine ⟨⟨⟨bound_init hl.1, strictMono_init hl.2⟩, ?_⟩, ?_⟩
        · have := hl.1 (Fin.last (n + 1))
          rw [Fin.succ_last] at this
          exact this
        · exact hl.2 (Fin.castSucc_lt_last _)
      · intro p _
        show (Fin.init (Fin.snoc p.1 p.2 : Fin (n + 2) → ℤ),
          (Fin.snoc p.1 p.2 : Fin (n + 2) → ℤ) (Fin.last _)) = p
        rw [Fin.init_snoc, Fin.snoc_last]
      · intro l _; exact Fin.snoc_init_self l
      · intro p _; rfl
    rw [hbad, hgood]
    ring

/-- **Fischer's theorem, one direction (formalized):** at strictly increasing rows the operator
formula counts monotone triangles. -/
theorem alpha_eq_mtNum : ∀ (n : ℕ) (k : Fin n → ℤ), StrictMono k → alpha n k = mtNum n k
  | 0, k, _ => by rw [alpha_zero]; simp [mtNum]
  | n + 1, k, hk => by
    rw [alpha_rec, S_strict n k hk, mtNum]
    push_cast
    refine sum_congr rfl fun l hl => ?_
    exact alpha_eq_mtNum n l (mem_interlace.mp hl).2

lemma rowMinus_strictMono (n j : ℕ) : StrictMono (rowMinus n j) := by
  intro a b hab
  rw [Fin.lt_iff_val_lt_val] at hab
  simp only [rowMinus]
  split_ifs <;> omega

/-- `A_{n,j}` is the number of monotone triangles with bottom row `(1, …, j−1, j+1, …, n)`. -/
theorem A_eq_mtNum (n j : ℕ) : A n j = mtNum (n - 1) (rowMinus n j) :=
  alpha_eq_mtNum _ _ (rowMinus_strictMono n j)

/-- **Conjecture 6 with the right-hand side stated through monotone-triangle counts.** -/
theorem riegler_conjecture6_mt (n i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ n - 1) :
    alpha (n + 1) (bRow n i)
      = - ∑ j ∈ Icc 1 n, ((j : ℚ) - i) * (mtNum (n - 1) (rowMinus n j) : ℚ) := by
  rw [riegler_conjecture6 n i hi1 hi2]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [A_eq_mtNum]

end MT
```

### `MTSmall.lean`

```lean
import MTMain
import Mathlib.Data.List.Sublists

/-!
# Non-vacuity checks (all by kernel evaluation, `decide +kernel`)

* `alpha` agrees with a computable recursion `alphaR` (from `alpha_rec`), so its values at small
  rows can be computed by the kernel;
* brute-force monotone-triangle counts `mtCount` (all triangular arrays with entries in
  `[k_1, k_n]`, filtered by the source's defining conditions) match `alpha` at several strictly
  increasing rows, including `A_n` and the refined numbers `A_{n,j}` for `n = 3, 4`;
* Conjecture 6 is checked by direct evaluation for `n = 2, 3, 4` (all `i`), independently of the
  general proof.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedTactic false

namespace MT

open Finset

/-- A computable copy of `alpha` via the recursion `α(n+1; k) = ∑^{(k)} α(n; l)`. -/
def alphaR : (n : ℕ) → (Fin n → ℤ) → ℚ
  | 0, _ => 1
  | n + 1, k => S n k (alphaR n)

theorem alpha_eq_alphaR : ∀ (n : ℕ) (k : Fin n → ℤ), alpha n k = alphaR n k
  | 0, k => alpha_zero k
  | n + 1, k => by
    rw [alpha_rec, alphaR]
    congr 1
    funext l
    exact alpha_eq_alphaR n l

/-! ## Brute-force monotone triangles -/

/-- Integers `a, a+1, …, b`. -/
def rangeZ (a b : ℤ) : List ℤ := (List.range (b - a + 1).toNat).map (fun t => a + t)

/-- Strictly increasing. -/
def strictInc : List ℤ → Bool
  | a :: b :: r => decide (a < b) && strictInc (b :: r)
  | _ => true

/-- Row `up` sits above row `low`: `low_j ≤ up_j ≤ low_{j+1}` and `|low| = |up| + 1`. -/
def interl (up low : List ℤ) : Bool :=
  decide (up.length + 1 = low.length) &&
    (List.range up.length).all fun j =>
      decide (low.getD j 0 ≤ up.getD j 0) && decide (up.getD j 0 ≤ low.getD (j + 1) 0)

/-- Rows (top to bottom) strictly increase and consecutive rows interlace
(weak increase along both diagonals). -/
def chainMT : List (List ℤ) → Bool
  | [] => true
  | [r] => strictInc r
  | up :: low :: rest => strictInc up && interl up low && chainMT (low :: rest)

/-- A monotone triangle given by its rows from top (length 1) to bottom. -/
def isMT (T : List (List ℤ)) : Bool :=
  decide ((T.headD []).length = 1) && chainMT T

/-- All candidate upper parts: lists of rows of lengths `1, …, m` with entries in `R`,
each row strictly increasing (a sublist of `R`). -/
def rowsUpTo (R : List ℤ) : ℕ → List (List (List ℤ))
  | 0 => [[]]
  | m + 1 => (rowsUpTo R m).flatMap fun rs => (R.sublistsLen (m + 1)).map fun r => rs ++ [r]

/-- Brute-force number of monotone triangles with bottom row `k` (entries of a monotone triangle
lie between `k_1` and `k_n`, so all of them are among the candidates). -/
def mtCount (k : List ℤ) : ℕ :=
  ((rowsUpTo (rangeZ (k.headD 0) (k.getLastD 0)) (k.length - 1)).filter
    fun rs => isMT (rs ++ [k])).length

theorem mt_1234 : mtCount [1, 2, 3, 4] = 42 := by decide +kernel
theorem mt_123 : mtCount [1, 2, 3] = 7 := by decide +kernel
theorem mt_A4 : mtCount [2, 3, 4] = 7 ∧ mtCount [1, 3, 4] = 14 ∧ mtCount [1, 2, 4] = 14 ∧
    mtCount [1, 2, 3] = 7 := by decide +kernel
theorem mt_misc : mtCount [1, 3, 5] = 26 := by decide +kernel

/-! ## `alpha` at strictly increasing rows equals the brute-force count -/

theorem alpha_1234 : alpha 4 ![1, 2, 3, 4] = (mtCount [1, 2, 3, 4] : ℚ) := by
  rw [alpha_eq_alphaR, mt_1234]; decide +kernel

theorem alpha_135 : alpha 3 ![1, 3, 5] = (mtCount [1, 3, 5] : ℚ) := by
  rw [alpha_eq_alphaR, mt_misc]; decide +kernel

theorem A4_values : A 4 1 = 7 ∧ A 4 2 = 14 ∧ A 4 3 = 14 ∧ A 4 4 = 7 := by
  unfold A
  simp only [show (4 : ℕ) - 1 = 3 from rfl, alpha_eq_alphaR]
  decide +kernel

theorem A4_mt : A 4 1 = mtCount [2, 3, 4] ∧ A 4 2 = mtCount [1, 3, 4] ∧
    A 4 3 = mtCount [1, 2, 4] ∧ A 4 4 = mtCount [1, 2, 3] := by
  obtain ⟨h1, h2, h3, h4⟩ := A4_values
  obtain ⟨m1, m2, m3, m4⟩ := mt_A4
  rw [h1, h2, h3, h4, m1, m2, m3, m4]; norm_num

/-! ## Direct evaluation of Conjecture 6 for small `n` -/

theorem conj6_n3 : ∀ i ∈ [1, 2], alphaR 4 (bRow 3 i)
    = - ∑ j ∈ Icc (1 : ℕ) 3, (((j : ℕ) : ℚ) - i) * alphaR 2 (rowMinus 3 j) := by decide +kernel

theorem conj6_n4 : ∀ i ∈ [1, 2, 3], alphaR 5 (bRow 4 i)
    = - ∑ j ∈ Icc (1 : ℕ) 4, (((j : ℕ) : ℚ) - i) * alphaR 3 (rowMinus 4 j) := by decide +kernel

theorem conj6_n4_values : alphaR 5 (bRow 4 1) = -63 ∧ alphaR 5 (bRow 4 2) = -21 ∧
    alphaR 5 (bRow 4 3) = 21 := by decide +kernel

end MT
```

### `MTAxioms.lean`

```lean
import MTFischer
import MTSmall

/-! # Cross-check of the two monotone-triangle counts, and the axiom report -/

namespace MT

/-- The recursive count `mtNum` agrees with the brute-force count `mtCount` at `(1,2,3,4)`. -/
theorem mtNum_1234 : (mtNum 4 ![1, 2, 3, 4] : ℚ) = mtCount [1, 2, 3, 4] := by
  rw [← alpha_eq_mtNum 4 ![1, 2, 3, 4] (Fin.strictMono_iff_lt_succ.mpr (by decide)), alpha_1234]

end MT

#print axioms MT.riegler_conjecture6
#print axioms MT.riegler_conjecture6_mt
#print axioms MT.alpha_eq_mtNum
#print axioms MT.alpha_rec
#print axioms MT.window_identity
#print axioms MT.alpha_refl_shift
#print axioms MT.checkW1
#print axioms MT.checkW3
#print axioms MT.check_ctrl2
#print axioms MT.alpha_1234
#print axioms MT.A4_mt
#print axioms MT.conj6_n4
#print axioms MT.mtNum_1234
```

