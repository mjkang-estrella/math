# Exact Lean source appendix for MathDB 369952

## Rows.lean

```lean
import Mathlib.Data.Sym.Sym2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Algebra.Rat

set_option maxHeartbeats 1300000

open Set
open scoped BigOperators

namespace Rigidity369952

abbrev Poly (V D : Type*) := MvPolynomial (V × D) ℚ
abbrev GenericField (V D : Type*) := FractionRing (Poly V D)
abbrev Edge (V : Type*) := {e : Sym2 V // ¬ e.IsDiag}

def orderedRow {V D R : Type*} [SubNegMonoid R] [DecidableEq V]
    (p : V × D → R) (a b : V) (w : V × D) : R :=
  (if w.1 = a then p (a,w.2) - p (b,w.2) else 0) +
  (if w.1 = b then p (b,w.2) - p (a,w.2) else 0)

-- The lift is independent of the representative of the unordered pair.
def edgeRow {V D R : Type*} [AddCommGroup R] [DecidableEq V]
    (p : V × D → R) (e : Sym2 V) : V × D → R :=
  Sym2.lift ⟨orderedRow p, fun _a _b => funext fun _w => add_comm _ _⟩ e

@[simp] theorem edgeRow_pair {V D R : Type*} [AddCommGroup R] [DecidableEq V]
    (p : V × D → R) (a b : V) :
    edgeRow p s(a,b) = orderedRow p a b := rfl

theorem edgeRow_map {V D R S : Type*} [AddCommGroup R] [AddCommGroup S] [DecidableEq V]
    (f : R →+ S) (p : V × D → R) (e : Sym2 V) (w : V × D) :
    f (edgeRow p e w) = edgeRow (f ∘ p) e w := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [edgeRow_pair, orderedRow, Function.comp_apply]
    split <;> split <;> simp [map_sub]

noncomputable def genericPosition {V D : Type*} (w : V × D) : GenericField V D :=
  algebraMap (Poly V D) (GenericField V D) (MvPolynomial.X w)

noncomputable def genericRow {V D : Type*} [DecidableEq V] (e : Edge V) :
    V × D → GenericField V D :=
  edgeRow genericPosition e.1

noncomputable def genericRank {V D : Type*} [Finite V] [Finite D] [DecidableEq V]
    (E : Set (Edge V)) : ℕ :=
  Module.finrank (GenericField V D)
    (Submodule.span (GenericField V D) (genericRow (D := D) '' E))

def GenericIndependent {V D : Type*} [DecidableEq V] (E : Set (Edge V)) : Prop :=
  LinearIndependent (GenericField V D) (fun e : E => genericRow (D := D) e.1)

noncomputable def realEmbedding {V D : Type*} (p : V × D → ℝ)
    (hp : AlgebraicIndependent ℚ p) : GenericField V D →+* ℝ := by
  let f : Poly V D →+* ℝ := (MvPolynomial.aeval p).toRingHom
  have hf : Function.Injective f := algebraicIndependent_iff_injective_aeval.mp hp
  exact IsFractionRing.lift (g := f) hf

@[simp] theorem realEmbedding_position {V D : Type*} (p : V × D → ℝ)
    (hp : AlgebraicIndependent ℚ p) (w : V × D) :
    realEmbedding p hp (genericPosition w) = p w := by
  simp [realEmbedding, genericPosition, IsFractionRing.lift_algebraMap]

theorem realEmbedding_row {V D : Type*} [DecidableEq V] (p : V × D → ℝ)
    (hp : AlgebraicIndependent ℚ p) (e : Edge V) (w : V × D) :
    realEmbedding p hp (genericRow e w) = edgeRow p e.1 w := by
  have hf : (realEmbedding p hp).toAddMonoidHom ∘ genericPosition = p :=
    funext (realEmbedding_position p hp)
  change (realEmbedding p hp).toAddMonoidHom (edgeRow genericPosition e.1 w) = _
  rw [edgeRow_map, hf]

theorem real_independent_iff {V D : Type*} [Finite V] [Finite D] [DecidableEq V] (p : V × D → ℝ)
    (hp : AlgebraicIndependent ℚ p) (E : Set (Edge V)) :
    LinearIndependent ℝ (fun e : E => edgeRow p e.1.1) ↔
      GenericIndependent (D := D) E := by
  let _ : Algebra (GenericField V D) ℝ := (realEmbedding p hp).toAlgebra
  have h := linearIndependent_algebraMap_comp_iff
    (S := ℝ) (v := fun e : E => genericRow (D := D) e.1)
  simp only [Function.comp_def, RingHom.algebraMap_toAlgebra, realEmbedding_row] at h
  exact h

#print axioms edgeRow_pair
#print axioms edgeRow_map
#print axioms realEmbedding_position
#print axioms realEmbedding_row
#print axioms real_independent_iff

end Rigidity369952
```

## Specialization.lean

```lean
import Rows
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.VectorSpace

open scoped BigOperators

namespace Rigidity369952

section Specialization
variable {R K S I J : Type*} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Field S]

theorem minor_ne_zero_of_specialization [Fintype I] [DecidableEq I]
    (f : R →+* S) (A : Matrix I I R) (h : (A.map f).det ≠ 0) :
    (A.map (algebraMap R K)).det ≠ 0 := by
  change ((algebraMap R K).mapMatrix A).det ≠ 0
  rw [← (algebraMap R K).map_det]
  intro hz
  have hR : A.det = 0 := (IsFractionRing.injective R K) (hz.trans (map_zero _).symm)
  apply h
  change (f.mapMatrix A).det = 0
  rw [← f.map_det, hR, map_zero]

theorem full_minor_of_independent [Fintype I] [Fintype J] [DecidableEq I]
    (A : Matrix I J S) (h : LinearIndependent S (fun i => A i)) :
    ∃ select : I → J, (A.submatrix id select).det ≠ 0 := by
  classical
  have hr : A.rank = Fintype.card I := LinearIndependent.rank_matrix (M := A) h
  have ht : Submodule.span S (Set.range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← A.rank_eq_finrank_span_cols, hr, Module.finrank_fintype_fun_eq_card]
  let t : Set (I → S) := (linearIndepOn_empty S id).extend (Set.empty_subset (Set.range A.col))
  let B : Module.Basis t S (I → S) :=
    Module.Basis.extendLe (linearIndepOn_empty S id) (Set.empty_subset _) ht.ge
  have hB := Module.Basis.extendLe_subset (linearIndepOn_empty S id) (Set.empty_subset _) ht.ge
  have hJ (b : t) : ∃ j : J, A.col j = B b := hB ⟨b, rfl⟩
  choose select hselect using hJ
  let _ : Finite t := Module.Finite.finite_basis B
  let _ : Fintype t := Fintype.ofFinite t
  have he : Fintype.card I = Fintype.card t := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fintype_fun_eq_card]
  let e := Fintype.equivOfCardEq he
  refine ⟨select ∘ e, ?_⟩
  apply isUnit_iff_ne_zero.mp
  rw [← Matrix.isUnit_iff_isUnit_det]
  apply Matrix.linearIndependent_cols_iff_isUnit.mp
  have hi := B.linearIndependent.comp e e.injective
  have heq : (A.submatrix id (select ∘ e)).col = B ∘ e :=
    funext fun i => hselect (e i)
  rwa [heq]

theorem independent_of_specialization [Fintype I] [Fintype J]
    (f : R →+* S) (A : Matrix I J R)
    (h : LinearIndependent S (fun i => (A.map f) i)) :
    LinearIndependent K (fun i => (A.map (algebraMap R K)) i) := by
  classical
  obtain ⟨select, hs⟩ := full_minor_of_independent (A.map f) h
  have hdet : ((A.submatrix id select).map (algebraMap R K)).det ≠ 0 :=
    minor_ne_zero_of_specialization f (A.submatrix id select) hs
  have hi := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  rw [linearIndependent_iff'] at hi ⊢
  intro s c hc i him
  apply hi s c _ i him
  ext j
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Matrix.map_apply,
    Matrix.submatrix_apply, id_eq] using congrFun hc (select j)

#print axioms minor_ne_zero_of_specialization
#print axioms full_minor_of_independent
#print axioms independent_of_specialization

end Specialization
end Rigidity369952
```

## Evaluation.lean

```lean
import Specialization
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace Rigidity369952

section Evaluation

variable {R S D : Type*} [CommRing R] [CommRing S] [Fintype D]

def bary (p : D → R) : Option D → R
  | none => 1 - ∑ i, p i
  | some i => p i

theorem map_bary (f : R →+* S) (p : D → R) (k : Option D) :
    f (bary p k) = bary (f ∘ p) k := by
  cases k <;> simp [bary, map_sum]

theorem bary_sum (p : D → R) : ∑ i, bary p i = 1 := by
  rw [Fintype.sum_option]
  simp [bary]

end Evaluation

section RationalWitness

variable {D : Type*} [Fintype D] [DecidableEq D]

private def vertexPoint (a : Option D) (i : D) : ℚ :=
  if some i = a then 1 else 0

private theorem bary_vertex (a b : Option D) :
    bary (vertexPoint (D := D) a) b = if b = a then 1 else 0 := by
  cases a <;> cases b <;> simp [bary, vertexPoint]

def midpoint : Sym2 (Option D) → D → ℚ :=
  Sym2.lift ⟨fun a b i => (vertexPoint a i + vertexPoint b i) / 2,
    fun a b => funext fun i => congrArg (· / 2) (add_comm (vertexPoint a i) (vertexPoint b i))⟩

private def midBary (e : Sym2 (Option D)) (i : Option D) := bary (midpoint e) i

private theorem midBary_mk (a b i : Option D) :
    midBary s(a,b) i =
      ((if i = a then (1 : ℚ) else 0) + (if i = b then 1 else 0)) / 2 := by
  have h (v w : D → ℚ) (k : Option D) :
      bary (fun i => (v i + w i) / 2) k = (bary v k + bary w k) / 2 := by
    cases k with
    | some i => rfl
    | none =>
      simp only [bary, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib]
      ring
  change bary (fun j => (vertexPoint a j + vertexPoint b j) / 2) i = _
  rw [h, bary_vertex, bary_vertex]

private theorem midBary_cross (a b : Option D) (hab : a ≠ b)
    (e : Sym2 (Option D)) :
    midBary e a * midBary e b = if e = s(a,b) then (1 : ℚ)/4 else 0 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [midBary_mk, midBary_mk]
    simp only [Sym2.eq_iff]
    by_cases au : a = u <;> by_cases av : a = v <;>
      by_cases bu : b = u <;> by_cases bv : b = v <;>
      simp_all <;> norm_num <;> aesop

private theorem midpoint_independent :
    LinearIndependent ℚ (fun e : Sym2 (Option D) =>
      fun k : Option D × Option D => midBary e k.1 * midBary e k.2) := by
  classical
  rw [linearIndependent_iff']
  intro S c h e he
  have hc (a b : Option D) :=
    congrFun h (a,b)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hc
  have off (a b : Option D) (hab : a ≠ b) (hm : s(a,b) ∈ S) : c s(a,b) = 0 := by
    have h' := hc a b
    simp_rw [midBary_cross a b hab, mul_ite, mul_zero] at h'
    have hz : c s(a,b) * (1/4 : ℚ) = 0 := by
      rw [Finset.sum_eq_single_of_mem s(a,b) hm (by intro x _ hx; simp [hx])] at h'
      simpa using h'
    exact (mul_eq_zero.mp hz).resolve_right (by norm_num)
  induction e using Sym2.inductionOn with
  | _ a b =>
    by_cases hab : a = b
    · subst b
      have hd := hc a a
      rw [Finset.sum_eq_single_of_mem s(a,a) he] at hd
      · norm_num [midBary_mk] at hd
        exact hd
      · intro x hx hxa
        induction x using Sym2.inductionOn with
        | _ u v =>
          by_cases huv : u = v
          · subst v
            have hua : a ≠ u := by
              intro h'
              subst u
              exact hxa rfl
            simp [midBary_mk, hua]
          · simp [off u v huv hx]
    · exact off a b hab he

private theorem bary_simplex_independent :
    LinearIndependent ℚ (fun a : Option D => bary (vertexPoint (D := D) a)) := by
  classical
  rw [linearIndependent_iff']
  intro S c h i hi
  have hz := congrFun h i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, bary_vertex,
    mul_ite, mul_one, mul_zero] at hz
  rw [Finset.sum_eq_single_of_mem i hi (by intro j _ hj; simp [Ne.symm hj])] at hz
  simpa using hz

end RationalWitness

section GenericEvaluation

variable {V D I : Type*} [Fintype D] [Fintype I] [DecidableEq D]

theorem generic_bary_independent (v : I ↪ V) (select : I ↪ Option D) :
    LinearIndependent (GenericField V D)
      (fun i : I => bary (fun j : D => genericPosition (v i,j))) := by
  classical
  let q : V → D → ℚ := Function.extend v (vertexPoint ∘ select) 0
  let f : Poly V D →+* ℚ := (MvPolynomial.aeval (fun w : V × D => q w.1 w.2)).toRingHom
  let A : Matrix I (Option D) (Poly V D) :=
    fun i => bary (fun j => MvPolynomial.X (v i,j))
  have hq (i : I) : q (v i) = vertexPoint (select i) :=
    Function.Injective.extend_apply v.injective _ _ _
  have hA : (fun i => (A.map f) i) = fun i => bary (vertexPoint (select i)) := by
    funext i k
    change f (bary (fun j => MvPolynomial.X (v i,j)) k) = _
    rw [map_bary]
    have hf : f ∘ (fun j => MvPolynomial.X (v i,j)) = q (v i) := by
      funext j
      simp [f]
    rw [hf, hq]
  have hi := independent_of_specialization (K := GenericField V D) f A
    (hA.symm ▸ (bary_simplex_independent (D := D)).comp select select.injective)
  have he : (fun i => (A.map (algebraMap (Poly V D) (GenericField V D))) i) =
      fun i => bary (fun j => genericPosition (v i,j)) := by
    funext i k
    exact map_bary (algebraMap (Poly V D) (GenericField V D))
      (fun j : D => MvPolynomial.X (v i,j)) k
  rwa [he] at hi

def quadricRow {R : Type*} [CommRing R] (p : D → R) (k : Option D × Option D) : R :=
  bary p k.1 * bary p k.2

theorem generic_quadric_independent (v : I ↪ V) (select : I ↪ Sym2 (Option D)) :
    LinearIndependent (GenericField V D)
      (fun i : I => quadricRow (fun j : D => genericPosition (v i,j))) := by
  classical
  let q : V → D → ℚ := Function.extend v (midpoint ∘ select) 0
  let f : Poly V D →+* ℚ := (MvPolynomial.aeval (fun w : V × D => q w.1 w.2)).toRingHom
  let A : Matrix I (Option D × Option D) (Poly V D) :=
    fun i => quadricRow (fun j => MvPolynomial.X (v i,j))
  have hq (i : I) : q (v i) = midpoint (select i) :=
    Function.Injective.extend_apply v.injective _ _ _
  have hA : (fun i => (A.map f) i) = fun i => quadricRow (midpoint (select i)) := by
    funext i k
    change f (quadricRow (fun j => MvPolynomial.X (v i,j)) k) = _
    have hf : f ∘ (fun j => MvPolynomial.X (v i,j)) = q (v i) := by
      funext j
      simp [f]
    simp only [quadricRow, map_mul, map_bary, hf, hq]
  have hi := independent_of_specialization (K := GenericField V D) f A
    (hA.symm ▸ (midpoint_independent (D := D)).comp select select.injective)
  have he : (fun i => (A.map (algebraMap (Poly V D) (GenericField V D))) i) =
      fun i => quadricRow (fun j => genericPosition (v i,j)) := by
    funext i k
    change algebraMap (Poly V D) (GenericField V D)
      (quadricRow (fun j => MvPolynomial.X (v i,j)) k) = _
    simp only [quadricRow, map_mul, map_bary]
    rfl
  rwa [he] at hi

omit [Fintype I] in
theorem midpoint_quadric_independent :
    LinearIndependent ℚ (fun e : Sym2 (Option D) => quadricRow (midpoint e)) :=
  midpoint_independent

omit [Fintype I] in
theorem midpoint_quadric_off_pair (a b : Option D) (hab : a ≠ b)
    (e : Sym2 (Option D)) (he : e ≠ s(a,b)) :
    quadricRow (midpoint e) (a,b) = 0 := by
  change midBary e a * midBary e b = 0
  rw [midBary_cross a b hab, ite_eq_right he]

omit [Fintype I] in
theorem midpoint_diagonal_bary (a k : Option D) :
    bary (midpoint s(a,a)) k = if k = a then 1 else 0 := by
  change midBary s(a,a) k = _
  rw [midBary_mk]
  split <;> norm_num

#print axioms midpoint_quadric_independent
#print axioms midpoint_quadric_off_pair
#print axioms midpoint_diagonal_bary
#print axioms generic_bary_independent
#print axioms generic_quadric_independent
#print axioms bary_sum

end GenericEvaluation
end Rigidity369952
```

## Force.lean

```lean
import Evaluation

open scoped BigOperators

namespace Rigidity369952

section Bipartite

variable {L R V D K : Type*} [Field K]

def leftVertex (v : L ⊕ R ↪ V) (i : L) := v (Sum.inl i)
def rightVertex (v : L ⊕ R ↪ V) (j : R) := v (Sum.inr j)

theorem cross_ne (v : L ⊕ R ↪ V) (i : L) (j : R) :
    leftVertex v i ≠ rightVertex v j := by
  intro h
  exact Sum.inl_ne_inr (v.injective h)

def bipEdge (v : L ⊕ R ↪ V) (e : L × R) : Edge V :=
  ⟨s(leftVertex v e.1, rightVertex v e.2),
    fun h => cross_ne v e.1 e.2 (Sym2.mk_isDiag_iff.mp h)⟩

theorem bipEdge_injective (v : L ⊕ R ↪ V) : Function.Injective (bipEdge v) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  have he := Sym2.eq_iff.mp (congrArg Subtype.val h)
  rcases he with h' | h'
  · exact Prod.ext (Sum.inl.inj (v.injective h'.1)) (Sum.inr.inj (v.injective h'.2))
  · exact (cross_ne v i j' h'.1).elim

variable [Fintype L] [Fintype R]

def ForceBalance (p : V × D → K) (v : L ⊕ R ↪ V) (c : L × R → K) : Prop :=
  (∀ i k, ∑ j, c (i,j) * (p (leftVertex v i,k) - p (rightVertex v j,k)) = 0) ∧
  (∀ j k, ∑ i, c (i,j) * (p (rightVertex v j,k) - p (leftVertex v i,k)) = 0)

theorem force_iff_stress [DecidableEq V] (p : V × D → K) (v : L ⊕ R ↪ V) (c : L × R → K) :
    ForceBalance p v c ↔ (∑ e, c e • edgeRow p (bipEdge v e).1) = 0 := by
  classical
  let S : V × D → K := ∑ e, c e • edgeRow p (bipEdge v e).1
  have hleft (i : L) (k : D) :
      S (leftVertex v i,k) =
        ∑ j, c (i,j) * (p (leftVertex v i,k) - p (rightVertex v j,k)) := by
    simp only [S, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
    simp only [bipEdge, edgeRow_pair, orderedRow]
    simp only [leftVertex, rightVertex, Function.Embedding.apply_eq_iff_eq, Sum.inl.injEq,
      Sum.inl_ne_inr, ite_false, add_zero, mul_ite, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hi'
      simp [Ne.symm hi']
    · simp
  have hright (j : R) (k : D) :
      S (rightVertex v j,k) =
        ∑ i, c (i,j) * (p (rightVertex v j,k) - p (leftVertex v i,k)) := by
    simp only [S, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
    simp only [bipEdge, edgeRow_pair, orderedRow]
    simp only [leftVertex, rightVertex, Function.Embedding.apply_eq_iff_eq, Sum.inr.injEq,
      Sum.inr_ne_inl, ite_false, zero_add, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [Ne.symm hj']
    · simp
  change _ ↔ S = 0
  constructor
  · rintro ⟨hl, hr⟩
    funext w
    obtain ⟨a,k⟩ := w
    by_cases ha : a ∈ Set.range v
    · obtain ⟨a', rfl⟩ := ha
      cases a' with
      | inl i => exact (hleft i k).trans (hl i k)
      | inr j => exact (hright j k).trans (hr j k)
    · have hl' (i : L) : a ≠ leftVertex v i :=
        fun he => ha ⟨Sum.inl i, he.symm⟩
      have hr' (j : R) : a ≠ rightVertex v j :=
        fun he => ha ⟨Sum.inr j, he.symm⟩
      simp [S, bipEdge, orderedRow, hl', hr']
  · intro h
    exact ⟨fun i k => (hleft i k).symm.trans (congrFun h (leftVertex v i,k)),
      fun j k => (hright j k).symm.trans (congrFun h (rightVertex v j,k))⟩

end Bipartite

section Augmented

variable {L R V D K : Type*} [Fintype L] [Fintype R] [Fintype D] [Field K]

def rowMarginal (c : L × R → K) (i : L) : K := ∑ j, c (i,j)
def colMarginal (c : L × R → K) (j : R) : K := ∑ i, c (i,j)

def AffineBalance (X : L → Option D → K) (Y : R → Option D → K)
    (c : L × R → K) : Prop :=
  (∀ i k, rowMarginal c i * X i k = ∑ j, c (i,j) * Y j k) ∧
  (∀ j k, colMarginal c j * Y j k = ∑ i, c (i,j) * X i k)

omit [Fintype L] [Fintype R] in
private theorem affine_axis {A B : Type*} [Fintype B]
    (X : A → D → K) (Y : B → D → K) (μ : A → B → K) (a : A) :
    (∀ k, ∑ b, μ a b * (X a k - Y b k) = 0) ↔
      ∀ k, (∑ b, μ a b) * bary (X a) k = ∑ b, μ a b * bary (Y b) k := by
  have hel (k : D) : (∑ b, μ a b * (X a k - Y b k) = 0) ↔
      (∑ b, μ a b) * X a k = ∑ b, μ a b * Y b k := by
    simp only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero, Finset.sum_mul]
  constructor
  · intro h k
    cases k with
    | some k => exact (hel k).mp (h k)
    | none =>
      have hs : (∑ b, μ a b) * (∑ k, X a k) = ∑ b, μ a b * (∑ k, Y b k) := by
        calc
          _ = ∑ k, (∑ b, μ a b) * X a k := Finset.mul_sum _ _ _
          _ = ∑ k, ∑ b, μ a b * Y b k :=
            Finset.sum_congr rfl (fun k _ => (hel k).mp (h k))
          _ = _ := by simp only [Finset.mul_sum]; exact Finset.sum_comm
      simp only [bary, mul_sub, mul_one, Finset.sum_sub_distrib, hs]
  · intro h k
    exact (hel k).mpr (h (some k))

theorem force_iff_affine (p : V × D → K) (v : L ⊕ R ↪ V) (c : L × R → K) :
    ForceBalance p v c ↔ AffineBalance
      (fun i => bary (fun k => p (leftVertex v i,k)))
      (fun j => bary (fun k => p (rightVertex v j,k))) c := by
  let X (i : L) (k : D) := p (leftVertex v i,k)
  let Y (j : R) (k : D) := p (rightVertex v j,k)
  constructor
  · rintro ⟨hl,hr⟩
    exact ⟨fun i => (affine_axis X Y (fun i j => c (i,j)) i).mp (hl i),
      fun j => (affine_axis Y X (fun j i => c (i,j)) j).mp (hr j)⟩
  · rintro ⟨hl,hr⟩
    exact ⟨fun i => (affine_axis X Y (fun i j => c (i,j)) i).mpr (hl i),
      fun j => (affine_axis Y X (fun j i => c (i,j)) j).mpr (hr j)⟩

omit [Fintype D] in
theorem stress_quadric_balance (X : L → Option D → K) (Y : R → Option D → K)
    (c : L × R → K) (h : AffineBalance X Y c) (a b : Option D) :
    ∑ i, rowMarginal c i * (X i a * X i b) =
      ∑ j, colMarginal c j * (Y j a * Y j b) := by
  calc
    _ = ∑ i, ∑ j, c (i,j) * (Y j a * X i b) := by
      simp only [← mul_assoc, h.1, Finset.sum_mul]
    _ = ∑ j, ∑ i, c (i,j) * (X i b * Y j a) := by
      rw [Finset.sum_comm]
      simp only [mul_comm (Y _ _) (X _ _)]
    _ = _ := by
      simp only [← mul_assoc, ← Finset.sum_mul, ← h.2]
      simp only [mul_assoc, mul_comm (Y _ b) (Y _ a)]

end Augmented

#print axioms bipEdge_injective
#print axioms force_iff_stress
#print axioms force_iff_affine
#print axioms stress_quadric_balance

end Rigidity369952
```

## Kernels.lean

```lean
import Force
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators

namespace Rigidity369952

noncomputable def embeddingOfCardLE {I J : Type*} [Fintype I] [Fintype J]
    (h : Fintype.card I ≤ Fintype.card J) : I ↪ J :=
  (Fintype.equivFin I).toEmbedding.trans
    ((Fin.castLEEmb h).trans (Fintype.equivFin J).symm.toEmbedding)

section Kernels

variable {I J K : Type*} [Fintype I] [Field K]

abbrev relationSpace (x : I → J → K) :=
  LinearMap.ker (Fintype.linearCombination K x)

theorem mem_relationSpace (x : I → J → K) (c : I → K) :
    c ∈ relationSpace x ↔ ∀ j, ∑ i, c i * x i j = 0 := by
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
  constructor
  · intro h j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun h j
  · intro h
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h j

theorem relation_zero_of_support (x : I → J → K) (c : I → K)
    {P : I → Prop} [DecidablePred P] (hc : c ∈ relationSpace x)
    (hP : ∀ i, ¬ P i → c i = 0)
    (hi : LinearIndependent K (fun i : {i // P i} => x i.1)) : c = 0 := by
  classical
  have hs : ∑ i : {i // P i}, c i.1 • x i.1 = 0 := by
    rw [← Finset.subtype_univ P, Finset.sum_subtype_eq_sum_filter (fun i => c i • x i)]
    rw [Finset.sum_filter]
    have he : (∑ i, if P i then c i • x i else 0) = ∑ i, c i • x i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : P i <;> simp [h, hP]
    rw [he]
    exact (Fintype.linearCombination_apply K x c).symm.trans hc
  have hz := Fintype.linearIndependent_iff.mp hi (fun i => c i.1) hs
  funext i
  by_cases h : P i
  · exact hz ⟨i,h⟩
  · exact hP i h

theorem relation_finrank_add (x : I → J → K) [Fintype J]
    (h : Submodule.span K (Set.range x) = ⊤) :
    Module.finrank K (relationSpace x) + Fintype.card J = Fintype.card I := by
  have hr := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination K x)
  rw [Fintype.range_linearCombination, h, finrank_top,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, add_comm] at hr
  exact hr

theorem relation_has_nonzero (x : I → J → K) (h : 0 < Module.finrank K (relationSpace x)) :
    ∃ c : I → K, c ∈ relationSpace x ∧ c ≠ 0 := by
  obtain ⟨c,hc⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  exact ⟨c,c.2,fun he => hc (Subtype.ext he)⟩

theorem relation_line (x : I → J → K) (h : Module.finrank K (relationSpace x) = 1)
    (c : I → K) (hc : c ∈ relationSpace x) (hn : c ≠ 0) :
    ∀ y : I → K, y ∈ relationSpace x → ∃ a : K, y = a • c := by
  let c' : relationSpace x := ⟨c,hc⟩
  have hn' : c' ≠ 0 := fun he => hn (congrArg Subtype.val he)
  have hs := (finrank_eq_one_iff_of_nonzero' c' hn').mp h
  intro y hy
  obtain ⟨a,ha⟩ := hs ⟨y,hy⟩
  exact ⟨a,(congrArg Subtype.val ha).symm⟩

end Kernels

section GenericKernels

variable {I V D : Type*} [Fintype I] [Fintype D] [DecidableEq D]

noncomputable def affineRow (v : I ↪ V) (i : I) : Option D → GenericField V D :=
  bary (fun j : D => genericPosition (v i,j))

theorem affine_subset_independent (v : I ↪ V) {P : I → Prop} [DecidablePred P]
    (hP : Fintype.card {i // P i} ≤ Fintype.card (Option D)) :
    LinearIndependent (GenericField V D) (fun i : {i // P i} => affineRow (D := D) v i.1) :=
  generic_bary_independent ((Function.Embedding.subtype P).trans v) (embeddingOfCardLE hP)

theorem affine_spans (v : I ↪ V) (h : Fintype.card (Option D) ≤ Fintype.card I) :
    Submodule.span (GenericField V D) (Set.range (affineRow (D := D) v)) = ⊤ := by
  let e := embeddingOfCardLE h
  have hi : LinearIndependent (GenericField V D) (affineRow (D := D) v ∘ e) :=
    generic_bary_independent (e.trans v) (Function.Embedding.refl _)
  have htop := hi.span_eq_top_of_card_eq_finrank'
    (Module.finrank_fintype_fun_eq_card (R := GenericField V D) (η := Option D)).symm
  exact top_unique (htop ▸ Submodule.span_mono (Set.range_comp_subset_range _ _))

theorem affine_kernel_finrank (v : I ↪ V) (h : Fintype.card (Option D) ≤ Fintype.card I) :
    Module.finrank (GenericField V D) (relationSpace (affineRow (D := D) v)) =
      Fintype.card I - Fintype.card (Option D) := by
  have hf := relation_finrank_add (affineRow (D := D) v) (affine_spans v h)
  omega

theorem affine_kernel_full_support (v : I ↪ V)
    (h : Fintype.card I = Fintype.card (Option D) + 1)
    (c : I → GenericField V D) (hc : c ∈ relationSpace (affineRow v)) (hn : c ≠ 0) :
    ∀ i, c i ≠ 0 := by
  classical
  intro i hzero
  have hcard := Fintype.card_subtype_compl (fun j : I => j = i)
  rw [Fintype.card_subtype_eq i] at hcard
  have hle : Fintype.card {j : I // ¬ j = i} ≤ Fintype.card (Option D) := by omega
  refine hn (relation_zero_of_support _ c hc ?_ (affine_subset_independent v hle))
  intro j hj
  exact (not_not.mp hj).symm ▸ hzero

theorem affine_kernel_two_zero (v : I ↪ V)
    (h : Fintype.card I = Fintype.card (Option D) + 2)
    (c : I → GenericField V D) (hc : c ∈ relationSpace (affineRow v))
    {i j : I} (hij : i ≠ j) (hi : c i = 0) (hj : c j = 0) : c = 0 := by
  classical
  have hcard := Fintype.card_subtype_compl (fun k : I => k = i ∨ k = j)
  rw [Fintype.card_subtype_eq_or_eq_of_ne hij] at hcard
  have hle : Fintype.card {k : I // ¬ (k = i ∨ k = j)} ≤ Fintype.card (Option D) := by omega
  refine relation_zero_of_support _ c hc ?_ (affine_subset_independent v hle)
  intro k hk
  rcases not_not.mp hk with rfl | rfl
  · exact hi
  · exact hj

end GenericKernels

#print axioms relation_zero_of_support
#print axioms relation_finrank_add
#print axioms relation_line
#print axioms affine_kernel_finrank
#print axioms affine_kernel_full_support
#print axioms affine_kernel_two_zero

end Rigidity369952
```

## BipartiteStress.lean

```lean
import Kernels

open scoped BigOperators

namespace Rigidity369952

section BipartiteStress

variable {L R V D : Type*} [Fintype L] [Fintype R] [Fintype D] [DecidableEq V]

local notation "F" => GenericField V D

def leftEmbedding (v : L ⊕ R ↪ V) : L ↪ V :=
  ⟨leftVertex v, fun _ _ h => Sum.inl.inj (v.injective h)⟩

def rightEmbedding (v : L ⊕ R ↪ V) : R ↪ V :=
  ⟨rightVertex v, fun _ _ h => Sum.inr.inj (v.injective h)⟩

noncomputable def crossRows (v : L ⊕ R ↪ V) (e : L × R) : V × D → F :=
  genericRow (bipEdge v e)

noncomputable abbrev stressSpace (v : L ⊕ R ↪ V) := relationSpace (crossRows (D := D) v)

theorem stress_iff_affineBalance (v : L ⊕ R ↪ V) (μ : L × R → F) :
    μ ∈ stressSpace v ↔ AffineBalance (affineRow (leftEmbedding v)) (affineRow (rightEmbedding v)) μ := by
  change Fintype.linearCombination F (crossRows v) μ = 0 ↔ _
  rw [Fintype.linearCombination_apply]
  exact (force_iff_stress genericPosition v μ).symm.trans
    (force_iff_affine genericPosition v μ)

omit [DecidableEq V] in
private theorem coeff_sum_zero {I : Type*} [Fintype I] (b : I ↪ V)
    (c : I → F) (hc : c ∈ relationSpace (affineRow b)) :
    ∑ i, c i = 0 := by
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset (Option D))) rfl
    (fun k _ => (mem_relationSpace _ _).mp hc k)
  rw [Finset.sum_comm] at hs
  simp only [← Finset.mul_sum, affineRow, bary_sum, mul_one, Finset.sum_const_zero] at hs
  exact hs

theorem stress_zero_marginals [DecidableEq D] (v : L ⊕ R ↪ V)
    (hq : Fintype.card (L ⊕ R) ≤ Fintype.card (Sym2 (Option D)))
    (μ : L × R → F) (hμ : μ ∈ stressSpace v) :
    (∀ i, rowMarginal μ i = 0) ∧ (∀ j, colMarginal μ j = 0) := by
  let coeff : L ⊕ R → F := Sum.elim (rowMarginal μ) (fun j => -colMarginal μ j)
  have hi := generic_quadric_independent v (embeddingOfCardLE hq)
  rw [Fintype.linearIndependent_iff] at hi
  have hb := (stress_iff_affineBalance v μ).mp hμ
  have hz : ∑ i, coeff i • quadricRow (fun k : D => genericPosition (v i,k)) = 0 := by
    funext k
    obtain ⟨a,b⟩ := k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fintype.sum_sum_type, coeff, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
    exact sub_eq_zero.mpr (stress_quadric_balance _ _ μ hb a b)
  have hc := hi coeff hz
  exact ⟨fun i => hc (Sum.inl i), fun j => neg_eq_zero.mp (hc (Sum.inr j))⟩

theorem stress_factorization [DecidableEq D] [Nonempty L]
    (v : L ⊕ R ↪ V) (hq : Fintype.card (L ⊕ R) ≤ Fintype.card (Sym2 (Option D)))
    (hL : Fintype.card L = Fintype.card (Option D) + 1) :
    ∃ lambda₀ : L → F, lambda₀ ∈ relationSpace (affineRow (leftEmbedding v)) ∧
      (∀ i, lambda₀ i ≠ 0) ∧
      ∀ μ : L × R → F, μ ∈ stressSpace v ↔
        ∃ c : R → F, c ∈ relationSpace (affineRow (rightEmbedding v)) ∧
          ∀ i j, μ (i,j) = lambda₀ i * c j := by
  let X := affineRow (D := D) (leftEmbedding v)
  let Y := affineRow (D := D) (rightEmbedding v)
  have hr : Module.finrank F (relationSpace X) = 1 := by
    rw [affine_kernel_finrank (leftEmbedding v) (by omega)]
    omega
  obtain ⟨lambda₀,hlambda,hne⟩ := relation_has_nonzero X (by omega)
  have hfull := affine_kernel_full_support (leftEmbedding v) hL lambda₀ hlambda hne
  refine ⟨lambda₀,hlambda,hfull,fun μ => ?_⟩
  constructor
  · intro hμ
    obtain ⟨ha,hb⟩ := stress_zero_marginals v hq μ hμ
    obtain ⟨hleft,hright⟩ := (stress_iff_affineBalance v μ).mp hμ
    have hcol (j : R) : (fun i => μ (i,j)) ∈ relationSpace X := by
      apply (mem_relationSpace _ _).mpr
      intro k
      exact (hright j k).symm.trans (by rw [hb j, zero_mul])
    obtain ⟨i₀⟩ := ‹Nonempty L›
    choose c hc using fun j => relation_line X hr lambda₀ hlambda hne _ (hcol j)
    have hfac (i : L) (j : R) : μ (i,j) = lambda₀ i * c j := by
      have he := congrFun (hc j) i
      simpa only [Pi.smul_apply, smul_eq_mul, mul_comm (c j)] using he
    refine ⟨c, (mem_relationSpace _ _).mpr ?_, hfac⟩
    intro k
    have hz : lambda₀ i₀ * (∑ j, c j * Y j k) = 0 := by
      simp only [Finset.mul_sum, ← mul_assoc, ← hfac]
      exact (hleft i₀ k).symm.trans (by rw [ha i₀, zero_mul])
    exact (mul_eq_zero.mp hz).resolve_left (hfull i₀)
  · rintro ⟨c,hc,hfac⟩
    have hc0 := coeff_sum_zero (rightEmbedding v) c hc
    have hlambda0 := coeff_sum_zero (leftEmbedding v) lambda₀ hlambda
    apply (stress_iff_affineBalance v μ).mpr
    constructor
    · intro i k
      have hrow : rowMarginal μ i = 0 := by
        simp only [rowMarginal, hfac, ← Finset.mul_sum, hc0, mul_zero]
      simp only [hrow, zero_mul, hfac, mul_assoc, ← Finset.mul_sum,
        (mem_relationSpace (affineRow (rightEmbedding v)) c).mp hc k, mul_zero]
    · intro j k
      have hcol : colMarginal μ j = 0 := by
        simp only [colMarginal, hfac, ← Finset.sum_mul, hlambda0, zero_mul]
      have hz : ∑ i, (lambda₀ i * c j) * X i k = 0 := by
        simp only [mul_comm (lambda₀ _) (c j), mul_assoc, ← Finset.mul_sum,
          (mem_relationSpace X lambda₀).mp hlambda k, mul_zero]
      simpa only [hcol, zero_mul, hfac] using hz.symm

end BipartiteStress

#print axioms stress_iff_affineBalance
#print axioms stress_zero_marginals
#print axioms stress_factorization

end Rigidity369952
```

## Circuits.lean

```lean
import BipartiteStress
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace Rigidity369952

noncomputable section

theorem independent_subtype_of_supported_zero {I J K : Type*} [Fintype I] [Field K]
    (x : I → J → K) (P : I → Prop) [DecidablePred P]
    (h : ∀ c : I → K, c ∈ relationSpace x → (∀ i, ¬P i → c i = 0) → c = 0) :
    LinearIndependent K (fun i : {i // P i} => x i.1) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let C (a : I) : K := if ha : P a then c ⟨a,ha⟩ else 0
  have hC : C ∈ relationSpace x := by
    change Fintype.linearCombination K x C = 0
    rw [Fintype.linearCombination_apply]
    have hsub (a : {a // P a}) : C a.1 = c a := by simp [C, a.2]
    have hh : (∑ a : {a // P a}, C a.1 • x a.1) = 0 := by
      simpa only [hsub] using hc
    rw [← Finset.subtype_univ P, Finset.sum_subtype_eq_sum_filter (fun a => C a • x a),
      Finset.sum_filter] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : P a <;> simp [C, ha]
  have hz := h C hC (fun a ha => dite_eq_right ha)
  have hi := congrFun hz i.1
  simpa [C, i.2] using hi

section RowRank

variable {L R V D : Type*} [Fintype L] [Fintype R] [Finite V] [Fintype D]
  [DecidableEq V]

local notation "F" => GenericField V D

abbrev completeBipartite (v : L ⊕ R ↪ V) : Set (Edge V) := Set.range (bipEdge v)

def GenericCircuit (D : Type*) {V : Type*} [DecidableEq V] (E : Set (Edge V)) : Prop :=
  ¬GenericIndependent (D := D) E ∧
    ∀ T ⊂ E, GenericIndependent (D := D) T

theorem bipartite_rank_add_stress (v : L ⊕ R ↪ V) :
    genericRank (D := D) (completeBipartite v) + Module.finrank F (stressSpace (D := D) v) =
      Fintype.card L * Fintype.card R := by
  let f := Fintype.linearCombination F (crossRows (D := D) v)
  have hn := LinearMap.finrank_range_add_finrank_ker f
  have hr : Set.range (crossRows (D := D) v) = genericRow '' completeBipartite v := by
    ext x
    exact ⟨fun ⟨e,he⟩ => ⟨bipEdge v e,⟨e,rfl⟩,he⟩,
      fun ⟨_,⟨e,rfl⟩,he⟩ => ⟨e,he⟩⟩
  change Module.finrank F (LinearMap.range (Fintype.linearCombination F _)) + _ = _ at hn
  rw [Fintype.range_linearCombination, hr, Module.finrank_fintype_fun_eq_card, Fintype.card_prod] at hn
  exact hn

omit [Finite V] [Fintype D] in
theorem generic_independent_bipartite_subset (v : L ⊕ R ↪ V) {E : Set (Edge V)}
    (hE : E ⊆ completeBipartite v)
    (h : ∀ μ : L × R → F, μ ∈ stressSpace (D := D) v → (∀ e, bipEdge v e ∉ E → μ e = 0) → μ = 0) :
    GenericIndependent (D := D) E := by
  classical
  let P (e : L × R) := bipEdge v e ∈ E
  have hi := independent_subtype_of_supported_zero (crossRows (D := D) v) P h
  let f : {e // P e} → E := fun e => ⟨bipEdge v e.1,e.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      exact Subtype.ext (bipEdge_injective v (congrArg Subtype.val he))
    · intro e
      obtain ⟨a,ha⟩ := hE e.2
      exact ⟨⟨a,show bipEdge v a ∈ E by rw [ha]; exact e.2⟩,Subtype.ext ha⟩
  let e := Equiv.ofBijective f hf
  have hh := hi.comp e.symm e.symm.injective
  have he (i : E) : bipEdge v (e.symm i).1 = i.1 := congrArg Subtype.val (e.apply_symm_apply i)
  have heq : (fun i : {e // P e} => crossRows (D := D) v i.1) ∘ e.symm =
      fun i : E => genericRow (D := D) i.1 := by
    funext i
    exact congrArg (genericRow (D := D)) (he i)
  rwa [heq] at hh

omit [Finite V] [Fintype D] in
private theorem bipartite_dependent_of_nonzero_stress (v : L ⊕ R ↪ V)
    (μ : L × R → F) (hμ : μ ∈ stressSpace (D := D) v) (hn : μ ≠ 0) :
    ¬GenericIndependent (D := D) (completeBipartite v) := by
  intro hi
  let f (e : L × R) : completeBipartite v := ⟨bipEdge v e,⟨e,rfl⟩⟩
  have hfinj : Function.Injective f := fun _ _ h => bipEdge_injective v (congrArg Subtype.val h)
  have hlin := hi.comp f hfinj
  apply hn
  exact funext (Fintype.linearIndependent_iff.mp hlin μ hμ)

end RowRank

section Dimensions

variable {L R V D : Type*} [Fintype L] [Fintype R] [Fintype D]
  [DecidableEq V] [DecidableEq D] [Nonempty L]

local notation "F" => GenericField V D

def BipartiteBounds : Prop := Fintype.card (L ⊕ R) ≤ Fintype.card (Sym2 (Option D))

theorem stress_space_equiv (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1) :
    Nonempty (relationSpace (affineRow (D := D) (rightEmbedding v)) ≃ₗ[F] stressSpace (D := D) v) := by
  obtain ⟨l,_,hne,hfactor⟩ := stress_factorization v hq hL
  let W := relationSpace (affineRow (D := D) (rightEmbedding v))
  let f : W →ₗ[F] stressSpace (D := D) v :=
    { toFun := fun c => ⟨fun e => l e.1 * c.1 e.2,
          (hfactor _).mpr ⟨c.1,c.2,fun _ _ => rfl⟩⟩
      map_add' := by intro c b; apply Subtype.ext; funext e; exact mul_add _ _ _
      map_smul' := by
        intro a c
        apply Subtype.ext
        funext e
        change l e.1 * (a * c.1 e.2) = a * (l e.1 * c.1 e.2)
        exact mul_left_comm _ _ _ }
  obtain ⟨i₀⟩ := ‹Nonempty L›
  refine ⟨LinearEquiv.ofBijective f ⟨?_,?_⟩⟩
  · intro c b he
    apply Subtype.ext
    funext j
    have hz := congrFun (congrArg Subtype.val he) (i₀,j)
    exact mul_left_cancel₀ (hne i₀) hz
  · intro μ
    obtain ⟨c,hc,hfac⟩ := (hfactor μ.1).mp μ.2
    exact ⟨⟨c,hc⟩,Subtype.ext (funext fun e => (hfac e.1 e.2).symm)⟩

theorem bipartite_stress_dim (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card (Option D) ≤ Fintype.card R) :
    Module.finrank F (stressSpace (D := D) v) = Fintype.card R - Fintype.card (Option D) := by
  obtain ⟨e⟩ := stress_space_equiv v hq hL
  exact e.finrank_eq.symm.trans (affine_kernel_finrank (rightEmbedding v) hR)

theorem bipartite_circuit [Finite V] (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 1) :
    GenericCircuit D (completeBipartite v) ∧
      genericRank (D := D) (completeBipartite v) = Fintype.card L * Fintype.card R - 1 := by
  have hf := bipartite_stress_dim v hq hL (by omega)
  have hn := bipartite_rank_add_stress (D := D) v
  have hdim : Module.finrank F (stressSpace (D := D) v) = 1 := by omega
  have hp : 0 < Module.finrank F (stressSpace (D := D) v) := by rw [hdim]; exact Nat.zero_lt_one
  obtain ⟨μ,hμ,hμn⟩ := relation_has_nonzero (crossRows (D := D) v) hp
  obtain ⟨l,_,hl,hfac⟩ := stress_factorization v hq hL
  refine ⟨⟨bipartite_dependent_of_nonzero_stress v μ hμ hμn, ?_⟩, by omega⟩
  intro E hE
  apply generic_independent_bipartite_subset v hE.le
  intro c hc hs
  obtain ⟨e,hem,hen⟩ := Set.exists_of_ssubset hE
  obtain ⟨a,rfl⟩ := hem
  obtain ⟨b,hb,hcb⟩ := (hfac c).mp hc
  have hz := hs a hen
  rw [hcb a.1 a.2] at hz
  have he := (mul_eq_zero.mp hz).resolve_left (hl a.1)
  have hb0 : b = 0 := by
    by_contra hn
    exact affine_kernel_full_support (rightEmbedding v) hR b hb hn a.2 he
  funext p
  simp [hcb p.1 p.2, hb0]

end Dimensions

#print axioms independent_subtype_of_supported_zero
#print axioms bipartite_rank_add_stress
#print axioms generic_independent_bipartite_subset
#print axioms stress_space_equiv
#print axioms bipartite_stress_dim
#print axioms bipartite_circuit

end
end Rigidity369952
```

## Double.lean

```lean
import Circuits

open scoped BigOperators

namespace Rigidity369952

noncomputable section

section Coordinate

variable {I K : Type*} [Field K]

def coordinate (W : Submodule K (I → K)) (i : I) : W →ₗ[K] K :=
  (LinearMap.proj i).comp W.subtype

@[simp] theorem coordinate_apply (W : Submodule K (I → K)) (i : I) (c : W) :
    coordinate W i c = c.1 i := rfl

theorem coordinate_kernel_finrank [Fintype I] [Nontrivial I] (W : Submodule K (I → K))
    (hdim : Module.finrank K W = 2)
    (htwo : ∀ (c : W) (i j : I), i ≠ j → c.1 i = 0 → c.1 j = 0 → c = 0)
    (j : I) : Module.finrank K (LinearMap.ker (coordinate W j)) = 1 := by
  have hn : ∃ c : W, coordinate W j c ≠ 0 := by
    by_contra! hz
    obtain ⟨k,hkj⟩ := exists_ne j
    have hi : Function.Injective (coordinate W k) := by
      intro a b hab
      have he : coordinate W k (a - b) = 0 := by rw [map_sub, hab, sub_self]
      exact sub_eq_zero.mp (htwo (a-b) j k hkj.symm
        (by simpa only [coordinate_apply] using hz (a-b))
        (by simpa only [coordinate_apply] using he))
    have hle := LinearMap.finrank_le_finrank_of_injective hi
    rw [hdim, Module.finrank_self] at hle
    omega
  obtain ⟨c,hc⟩ := hn
  have hsurj : Function.Surjective (coordinate W j) := by
    intro a
    refine ⟨(a / coordinate W j c) • c, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hc]
  have hf := LinearMap.finrank_range_add_finrank_ker (coordinate W j)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, hdim] at hf
  omega

end Coordinate

section Classes

variable {L R V D : Type*} [Fintype L] [Fintype R] [Fintype D]
  [DecidableEq V] [DecidableEq D] [Nonempty L] [Nontrivial R]

local notation "F" => GenericField V D

omit [Nontrivial R] in
theorem bipartite_two_column_zero (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 2)
    (μ : stressSpace (D := D) v) (e f : L × R) (h : e.2 ≠ f.2)
    (he : μ.1 e = 0) (hf : μ.1 f = 0) : μ = 0 := by
  obtain ⟨l,_,hl,hfac⟩ := stress_factorization v hq hL
  obtain ⟨c,hc,hμ⟩ := (hfac μ.1).mp μ.2
  rw [show μ.1 e = l e.1 * c e.2 from hμ e.1 e.2] at he
  rw [show μ.1 f = l f.1 * c f.2 from hμ f.1 f.2] at hf
  have hz := affine_kernel_two_zero (rightEmbedding v) hR c hc h
    ((mul_eq_zero.mp he).resolve_left (hl e.1)) ((mul_eq_zero.mp hf).resolve_left (hl f.1))
  apply Subtype.ext
  funext a
  change μ.1 (a.1,a.2) = 0
  rw [hμ a.1 a.2, hz]
  exact mul_zero _

theorem bipartite_stress_column_support (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 2)
    (j : R) :
    ∃ μ : stressSpace (D := D) v, ∀ e : L × R, μ.1 e = 0 ↔ e.2 = j := by
  let W := relationSpace (affineRow (D := D) (rightEmbedding v))
  have hdim : Module.finrank F W = 2 := by
    change Module.finrank F (relationSpace (affineRow (D := D) (rightEmbedding v))) = _
    rw [affine_kernel_finrank (rightEmbedding v) (by omega), hR]
    omega
  have htwo (c : W) (i k : R) (hik : i ≠ k) (hi : c.1 i = 0) (hk : c.1 k = 0) : c = 0 :=
    Subtype.ext (affine_kernel_two_zero (rightEmbedding v) hR c.1 c.2 hik hi hk)
  have hker := coordinate_kernel_finrank W hdim htwo j
  have hp : 0 < Module.finrank F (LinearMap.ker (coordinate W j)) := by rw [hker]; exact Nat.zero_lt_one
  have hnon : ∃ c : LinearMap.ker (coordinate W j), c ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := F)
      (M := ↥(LinearMap.ker (coordinate W j)))).mp hp
  obtain ⟨c,hc⟩ := hnon
  have hcz : c.1 ≠ 0 := fun h => hc (Subtype.ext h)
  obtain ⟨l,_,hl,hfac⟩ := stress_factorization v hq hL
  refine ⟨⟨fun e => l e.1 * c.1.1 e.2, (hfac _).mpr ⟨c.1.1,c.1.2,fun _ _ => rfl⟩⟩, ?_⟩
  intro e
  change l e.1 * c.1.1 e.2 = 0 ↔ e.2 = j
  have hj : c.1.1 j = 0 := c.2
  constructor
  · intro hz
    by_contra hn
    exact hcz (htwo c.1 e.2 j hn ((mul_eq_zero.mp hz).resolve_left (hl e.1)) hj)
  · rintro he
    rw [he, hj, mul_zero]

theorem bipartite_stress_column_classes (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 2)
    (e f : L × R) :
    e.2 = f.2 ↔ ∀ μ : stressSpace (D := D) v, μ.1 e = 0 ↔ μ.1 f = 0 := by
  constructor
  · intro he μ
    obtain ⟨l,_,hl,hfac⟩ := stress_factorization v hq hL
    obtain ⟨c,_,hc⟩ := (hfac μ.1).mp μ.2
    rw [show μ.1 e = l e.1 * c e.2 from hc e.1 e.2,
      show μ.1 f = l f.1 * c f.2 from hc f.1 f.2, he]
    simp only [mul_eq_zero, hl, false_or]
  · intro h
    obtain ⟨μ,hμ⟩ := bipartite_stress_column_support v hq hL hR e.2
    exact ((hμ f).mp ((h μ).mp ((hμ e).mpr rfl))).symm

omit [Nontrivial R] in
theorem bipartite_double_rank [Finite V] (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 2) :
    Module.finrank F (stressSpace (D := D) v) = 2 ∧
      genericRank (D := D) (completeBipartite v) = Fintype.card L * Fintype.card R - 2 := by
  have hdim := bipartite_stress_dim v hq hL (by omega)
  have hr := bipartite_rank_add_stress (D := D) v
  omega

end Classes

theorem biclique_bound (d t : ℕ) (hd : 5 ≤ d) (ht : t ≤ d+3) :
    BipartiteBounds (L := Fin (d+2)) (R := Fin t) (D := Fin d) := by
  unfold BipartiteBounds
  rw [Fintype.card_sum, Sym2.card]
  simp only [Fintype.card_fin, Fintype.card_option]
  rw [Nat.choose_two_right]
  have hsub : d + 1 + 1 - 1 = d + 1 := by omega
  rw [hsub]
  have hmul := Nat.mul_le_mul_right d hd
  have hlarge : 2 * (d + 2 + t) ≤ (d + 1 + 1) * (d + 1) := by nlinarith
  omega

theorem generic_Kss {V : Type*} [Finite V] [DecidableEq V] (d : ℕ) (hd : 5 ≤ d)
    (v : Fin (d+2) ⊕ Fin (d+2) ↪ V) :
    GenericCircuit (Fin d) (completeBipartite v) ∧
      genericRank (D := Fin d) (completeBipartite v) = (d+2)^2 - 1 := by
  simpa only [Fintype.card_fin, pow_two] using bipartite_circuit v
    (biclique_bound d (d+2) hd (by omega))
    (by simp [Nat.add_assoc]) (by simp [Nat.add_assoc])

theorem generic_Kssplus1 {V : Type*} [Finite V] [DecidableEq V] (d : ℕ) (hd : 5 ≤ d)
    (v : Fin (d+2) ⊕ Fin (d+3) ↪ V) :
    Module.finrank (GenericField V (Fin d)) (stressSpace (D := Fin d) v) = 2 ∧
      genericRank (D := Fin d) (completeBipartite v) = (d+2)*(d+3) - 2 := by
  simpa only [Fintype.card_fin] using bipartite_double_rank v
    (biclique_bound d (d+3) hd le_rfl)
    (by simp [Nat.add_assoc]) (by simp [Nat.add_assoc])

#print axioms coordinate_kernel_finrank
#print axioms bipartite_two_column_zero
#print axioms bipartite_stress_column_support
#print axioms bipartite_stress_column_classes
#print axioms bipartite_double_rank
#print axioms biclique_bound
#print axioms generic_Kss
#print axioms generic_Kssplus1

end
end Rigidity369952
```

## Seam.lean

```lean
import Double
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

namespace Rigidity369952

section ForceMoments

variable {V D K : Type*} [Fintype V] [DecidableEq V] [Field K]

def block (a : V) (x : D → K) (w : V × D) : K := if w.1 = a then x w.2 else 0

def netForce (i : D) : (V × D → K) →ₗ[K] K :=
  ∑ a : V, LinearMap.proj (a,i)

def moment (p : V × D → K) (i j : D) : (V × D → K) →ₗ[K] K :=
  ∑ a : V, (p (a,i) • LinearMap.proj (a,j) - p (a,j) • LinearMap.proj (a,i))

@[simp] theorem netForce_block (a : V) (x : D → K) (i : D) :
    netForce i (block a x) = x i := by
  simp [netForce, block]

@[simp] theorem moment_block (p : V × D → K) (a : V) (x : D → K) (i j : D) :
    moment p i j (block a x) = p (a,i) * x j - p (a,j) * x i := by
  simp only [moment, LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, block, mul_ite, mul_zero]
  rw [Finset.sum_sub_distrib]
  simp

theorem netForce_row (p : V × D → K) (e : Sym2 V) (i : D) :
    netForce i (edgeRow p e) = 0 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [edgeRow_pair]
    change netForce i (block a (fun k => p (a,k) - p (b,k)) +
      block b (fun k => p (b,k) - p (a,k))) = 0
    simp only [map_add, netForce_block]
    ring

theorem moment_row (p : V × D → K) (e : Sym2 V) (i j : D) :
    moment p i j (edgeRow p e) = 0 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [edgeRow_pair]
    change moment p i j (block a (fun k => p (a,k) - p (b,k)) +
      block b (fun k => p (b,k) - p (a,k))) = 0
    simp only [map_add, moment_block]
    ring

theorem span_force_moment (p : V × D → K) (E : Set (Edge V)) (f : V × D → K)
    (hf : f ∈ Submodule.span K ((fun e : Edge V => edgeRow p e.1) '' E)) :
    (∀ i, netForce i f = 0) ∧ ∀ i j, moment p i j f = 0 := by
  have aux (T : (V × D → K) →ₗ[K] K) (hT : ∀ e : Edge V, T (edgeRow p e.1) = 0) :
      T f = 0 := by
    have hle : Submodule.span K ((fun e : Edge V => edgeRow p e.1) '' E) ≤
        LinearMap.ker T := by
      apply Submodule.span_le.mpr
      rintro _ ⟨e,_,rfl⟩
      exact hT e
    exact hle hf
  exact ⟨fun i => aux _ (fun e => netForce_row p e.1 i),
    fun i j => aux _ (fun e => moment_row p e.1 i j)⟩

theorem two_vertex_force (p : V × D → K) (a b : V) (hab : a ≠ b)
    (f : V × D → K) (hs : ∀ v i, v ≠ a → v ≠ b → f (v,i) = 0)
    (hn : ∀ i, netForce i f = 0) (hm : ∀ i j, moment p i j f = 0)
    (k : D) (hk : p (a,k) ≠ p (b,k)) :
    ∃ c : K, f = c • edgeRow p s(a,b) := by
  have hblocks : f = block a (fun i => f (a,i)) + block b (fun i => f (b,i)) := by
    funext w
    obtain ⟨v,i⟩ := w
    by_cases ha : v = a
    · subst v
      simp [block, hab]
    · by_cases hb : v = b
      · subst v
        simp [block, ha]
      · simp [block, ha, hb, hs v i ha hb]
  have hbalance (i : D) : f (b,i) = - f (a,i) := by
    have hi := hn i
    rw [hblocks] at hi
    simp only [map_add, netForce_block] at hi
    exact eq_neg_of_add_eq_zero_right hi
  let delta (i : D) := p (a,i) - p (b,i)
  have hdet (i : D) : delta k * f (a,i) = delta i * f (a,k) := by
    have hi := hm k i
    rw [hblocks] at hi
    simp only [map_add, moment_block, hbalance] at hi
    unfold delta
    linear_combination hi
  let c := f (a,k) / delta k
  have hf (i : D) : f (a,i) = c * delta i := by
    change f (a,i) = (f (a,k) / delta k) * delta i
    rw [mul_comm, ← mul_div_assoc, eq_div_iff_mul_eq (sub_ne_zero.mpr hk)]
    exact (mul_comm _ _).trans (hdet i)
  refine ⟨c,?_⟩
  funext w
  obtain ⟨v,i⟩ := w
  rw [edgeRow_pair]
  by_cases ha : v = a
  · subst v
    simpa [orderedRow, hab, delta] using hf i
  · by_cases hb : v = b
    · subst v
      simp only [Pi.smul_apply, smul_eq_mul, orderedRow, ha, ite_false,
        ite_true, zero_add, hbalance, hf, delta]
      ring
    · simp [orderedRow, ha, hb, hs v i ha hb]

end ForceMoments

theorem generic_two_vertex_seam {V D : Type*} [Fintype V] [DecidableEq V]
    (E : Set (Edge V)) (a b : V) (hab : a ≠ b) (k : D)
    (f : V × D → GenericField V D)
    (hf : f ∈ Submodule.span (GenericField V D) (genericRow (D := D) '' E))
    (hs : ∀ v i, v ≠ a → v ≠ b → f (v,i) = 0) :
    ∃ c : GenericField V D, f = c • edgeRow genericPosition s(a,b) := by
  obtain ⟨hn, hm⟩ := span_force_moment genericPosition E f hf
  apply two_vertex_force genericPosition a b hab f hs hn hm k
  intro he
  exact hab (congrArg Prod.fst (MvPolynomial.X_injective
    (IsFractionRing.injective (Poly V D) (GenericField V D) he)))

#print axioms span_force_moment
#print axioms two_vertex_force
#print axioms generic_two_vertex_seam

end Rigidity369952
```

## NativeRank.lean

```lean
import Kernels

open Set

namespace Rigidity369952

section SpanRank

variable {I J K L : Type*} [Finite J] [Field K] [Field L]

private theorem spanRank_le_of_independence_transfer (x : I → J → K) (y : I → J → L)
    (h : ∀ (m : ℕ) (select : Fin m → I),
      LinearIndependent K (x ∘ select) → LinearIndependent L (y ∘ select)) :
    Module.finrank K (Submodule.span K (range x)) ≤
      Module.finrank L (Submodule.span L (range y)) := by
  obtain ⟨b,hb,_,hind⟩ := Submodule.exists_fun_fin_finrank_span_eq K (range x)
  choose select hs using hb
  have hx : x ∘ select = b := funext hs
  have hy := h _ select (hx.symm ▸ hind)
  let M := Submodule.span L (range y)
  let z (i : _) : M := ⟨y (select i), Submodule.subset_span ⟨select i,rfl⟩⟩
  have hz : LinearIndependent L z := by
    rw [← LinearMap.linearIndependent_iff_of_injOn M.subtype Subtype.val_injective.injOn]
    exact hy
  simpa only [Fintype.card_fin] using hz.fintype_card_le_finrank

end SpanRank

section RealRank
variable {V D : Type*} [Finite V] [Finite D] [DecidableEq V]

noncomputable def realRowRank (p : V × D → ℝ) (E : Set (Edge V)) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ ((fun e : Edge V => edgeRow p e.1) '' E))

theorem real_rank_eq_genericRank (p : V × D → ℝ) (hp : AlgebraicIndependent ℚ p)
    (E : Set (Edge V)) : realRowRank p E = genericRank (D := D) E := by
  let X (e : E) := genericRow (D := D) e.1
  let Y (e : E) := edgeRow p e.1.1
  have hx : range X = genericRow (D := D) '' E := by
    ext x
    exact ⟨fun ⟨e,h⟩ => ⟨e.1,e.2,h⟩,fun ⟨e,he,h⟩ => ⟨⟨e,he⟩,h⟩⟩
  have hy : range Y = (fun e : Edge V => edgeRow p e.1) '' E := by
    ext x
    exact ⟨fun ⟨e,h⟩ => ⟨e.1,e.2,h⟩,fun ⟨e,he,h⟩ => ⟨⟨e,he⟩,h⟩⟩
  have equiv (m : ℕ) (select : Fin m → E) :
      LinearIndependent ℝ (Y ∘ select) ↔
        LinearIndependent (GenericField V D) (X ∘ select) := by
    let _ : Algebra (GenericField V D) ℝ := (realEmbedding p hp).toAlgebra
    have h := linearIndependent_algebraMap_comp_iff (S := ℝ) (v := X ∘ select)
    simpa only [Function.comp_def, RingHom.algebraMap_toAlgebra, X, Y, realEmbedding_row] using h
  unfold realRowRank genericRank
  rw [← hx, ← hy]
  exact le_antisymm (spanRank_le_of_independence_transfer Y X (fun m s => (equiv m s).mp))
    (spanRank_le_of_independence_transfer X Y (fun m s => (equiv m s).mpr))

#print axioms real_rank_eq_genericRank

end RealRank
end Rigidity369952
```

## SecantEvaluation.lean

```lean
import Kernels

open scoped BigOperators

namespace Rigidity369952

noncomputable section

def secantQuadric {D K : Type*} [Fintype D] [CommRing K]
    (p q : D → K) (k : Option D × Option D) : K :=
  (bary p k.1 - bary q k.1) * (bary p k.2 - bary q k.2)

private def appendQuadric {D K I : Type*} [Fintype D] [CommRing K]
    (p : I → D → K) (a b : I) : Option I → (Option D × Option D → K) :=
  fun o => o.casesOn' (secantQuadric (p a) (p b)) (fun i => quadricRow (p i))

private theorem map_appendQuadric {D K S I : Type*} [Fintype D] [CommRing K] [CommRing S]
    (f : K →+* S) (p : I → D → K) (a b : I) (i : Option I) (k : Option D × Option D) :
    f (appendQuadric p a b i k) = appendQuadric (fun j => f ∘ p j) a b i k := by
  cases i <;> simp only [appendQuadric, Option.casesOn', secantQuadric, quadricRow,
    map_mul, map_sub, map_bary]

private theorem pair_with_prescribed_images {A B : Type*} [DecidableEq B] (q : A ↪ B)
    (a b : A) (hab : a ≠ b) (x y : B) (hxy : x ≠ y) :
    ∃ f : A ↪ B, f a = x ∧ f b = y := by
  let f := q.trans (Equiv.swap (q a) x).toEmbedding
  have hx : f a = x := Equiv.swap_apply_left _ _
  have hz : x ≠ f b := fun h => hab (f.injective (hx.trans h))
  refine ⟨f.trans (Equiv.swap (f b) y).toEmbedding, ?_, ?_⟩
  · change Equiv.swap (f b) y (f a) = x
    rw [hx, Equiv.swap_apply_of_ne_of_ne hz hxy]
  · exact Equiv.swap_apply_left _ _

private theorem rational_secant_independent {I D : Type*} [Fintype I] [Fintype D] [DecidableEq D]
    (a b : I) (hab : a ≠ b) (x y : Option D) (hxy : x ≠ y)
    (hcard : Fintype.card I < Fintype.card (Sym2 (Option D))) :
    ∃ p : I → D → ℚ, LinearIndependent ℚ (appendQuadric p a b) := by
  classical
  let S := {e : Sym2 (Option D) // e ≠ s(x,y)}
  let X : S := ⟨s(x,x),fun h => by
    have he := Sym2.eq_iff.mp h
    exact hxy (he.elim (fun h => h.2) (fun h => h.1))⟩
  let Y : S := ⟨s(y,y),fun h => by
    have he := Sym2.eq_iff.mp h
    exact hxy (he.elim (fun h => h.1.symm) (fun h => h.2.symm))⟩
  have hXY : X ≠ Y := fun he => by
    have h := Sym2.eq_iff.mp (congrArg Subtype.val he)
    exact hxy (h.elim (fun h => h.1) (fun h => h.1))
  have hc := Fintype.card_subtype_compl (fun e : Sym2 (Option D) => e = s(x,y))
  rw [Fintype.card_subtype_eq] at hc
  have hl : Fintype.card I ≤ Fintype.card S := by change Fintype.card I ≤ Fintype.card {e : Sym2 (Option D) // ¬ e = s(x,y)}; omega
  obtain ⟨f,hfa,hfb⟩ := pair_with_prescribed_images (embeddingOfCardLE hl) a b hab X Y hXY
  let g : I ↪ Sym2 (Option D) := f.trans (Function.Embedding.subtype _)
  let p := midpoint ∘ g
  refine ⟨p, (linearIndependent_option).mpr ⟨?_,?_⟩⟩
  · exact (midpoint_quadric_independent (D := D)).comp g g.injective
  · change secantQuadric (p a) (p b) ∉ Submodule.span ℚ (Set.range (fun i => quadricRow (p i)))
    intro hm
    let f₀ : (Option D × Option D → ℚ) →ₗ[ℚ] ℚ := LinearMap.proj (x,y)
    have hle : Submodule.span ℚ (Set.range (fun i => quadricRow (p i))) ≤ LinearMap.ker f₀ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact midpoint_quadric_off_pair x y hxy (g i) (f i).2
    have hz : secantQuadric (p a) (p b) (x,y) = 0 := hle hm
    have hga : g a = s(x,x) := congrArg Subtype.val hfa
    have hgb : g b = s(y,y) := congrArg Subtype.val hfb
    norm_num [secantQuadric, p, hga, hgb, midpoint_diagonal_bary, hxy, Ne.symm hxy] at hz

theorem generic_secant_notMem_quadric_span {I V D : Type*}
    [Fintype I] [Fintype D] [DecidableEq D] (v : I ↪ V)
    (a b : I) (hab : a ≠ b) (x y : Option D) (hxy : x ≠ y)
    (hcard : Fintype.card I < Fintype.card (Sym2 (Option D))) :
    let p (i : I) (j : D) := genericPosition (v i,j)
    secantQuadric (p a) (p b) ∉ Submodule.span (GenericField V D)
      (Set.range (fun i => quadricRow (p i))) := by
  classical
  obtain ⟨q,hq⟩ := rational_secant_independent a b hab x y hxy hcard
  let witness : V → D → ℚ := Function.extend v q 0
  let f : Poly V D →+* ℚ := (MvPolynomial.aeval (fun w : V × D => witness w.1 w.2)).toRingHom
  let pPoly (i : I) (j : D) : Poly V D := MvPolynomial.X (v i,j)
  let A : Matrix (Option I) (Option D × Option D) (Poly V D) := appendQuadric pPoly a b
  have he (i : I) : f ∘ pPoly i = q i := by
    funext j
    have hw := Function.Injective.extend_apply v.injective q (0 : V → D → ℚ) i
    simp [f,pPoly,witness,hw]
  have heq : (fun i => (A.map f) i) = appendQuadric q a b := by
    funext i k
    exact (map_appendQuadric f pPoly a b i k).trans
      (congrArg (fun p => appendQuadric p a b i k) (funext he))
  have hLI := independent_of_specialization (K := GenericField V D) f A (heq.symm ▸ hq)
  let p (i : I) (j : D) := genericPosition (v i,j)
  have hf : (fun i => (A.map (algebraMap (Poly V D) (GenericField V D))) i) =
      appendQuadric p a b := by
    funext i k
    exact map_appendQuadric (algebraMap (Poly V D) (GenericField V D)) pPoly a b i k
  rw [hf] at hLI
  exact (linearIndependent_option.mp hLI).2

#print axioms generic_secant_notMem_quadric_span

end
end Rigidity369952
```

## Separation.lean

```lean
import Seam
import SecantEvaluation

open scoped BigOperators

namespace Rigidity369952

noncomputable section

section Signal
variable {V D K : Type*} [Fintype V] [DecidableEq V] [Fintype D] [Field K]

private def direction (x : D → K) : Option D → K
  | none => -(∑ i, x i)
  | some i => x i

private theorem direction_sub (x y : D → K) (k : Option D) :
    direction (fun i => x i - y i) k = bary x k - bary y k := by
  cases k with
  | some i => rfl
  | none =>
    simp only [direction, bary, Finset.sum_sub_distrib]
    ring

private def directionAt (a : V) : Option D → ((V × D → K) →ₗ[K] K)
  | none => -(∑ i : D, LinearMap.proj (a,i))
  | some i => LinearMap.proj (a,i)

omit [Fintype V] in
private theorem directionAt_block (a b : V) (x : D → K) (k : Option D) :
    directionAt a k (block b x) = if a = b then direction x k else 0 := by
  cases k <;> by_cases h : a = b <;> simp [directionAt,direction,block,h]

private def signal (p : V × D → K) (sign : V → K) :
    (V × D → K) →ₗ[K] (Option D × Option D → K) :=
  LinearMap.pi fun k => ∑ a : V,
    ((sign a * bary (fun i => p (a,i)) k.1) • directionAt a k.2 +
      (sign a * bary (fun i => p (a,i)) k.2) • directionAt a k.1)

private theorem signal_block (p : V × D → K) (sgn : V → K)
    (a : V) (x : D → K) (k : Option D × Option D) :
    signal p sgn (block a x) k =
      (sgn a * bary (fun i => p (a,i)) k.1) * direction x k.2 +
      (sgn a * bary (fun i => p (a,i)) k.2) * direction x k.1 := by
  simp only [signal, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, directionAt_block]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

private theorem signal_cross (p : V × D → K) (sgn : V → K) (a b : V)
    (ha : sgn a = 1) (hb : sgn b = -1) :
    signal p sgn (edgeRow p s(a,b)) =
      (2 : K) • (quadricRow (fun i => p (a,i)) - quadricRow (fun i => p (b,i))) := by
  rw [edgeRow_pair]
  change signal p sgn (block a (fun i => p (a,i) - p (b,i)) +
    block b (fun i => p (b,i) - p (a,i))) = _
  rw [map_add]
  funext k
  simp only [Pi.add_apply, signal_block, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    direction_sub, ha, hb, quadricRow]
  ring

private theorem signal_same (p : V × D → K) (sgn : V → K) (a b : V)
    (h : sgn a = sgn b) :
    signal p sgn (edgeRow p s(a,b)) =
      (2 * sgn a) • secantQuadric (fun i => p (a,i)) (fun i => p (b,i)) := by
  rw [edgeRow_pair]
  change signal p sgn (block a (fun i => p (a,i) - p (b,i)) +
    block b (fun i => p (b,i) - p (a,i))) = _
  rw [map_add]
  funext k
  simp only [Pi.add_apply, signal_block, Pi.smul_apply, smul_eq_mul,
    direction_sub, ← h, secantQuadric]
  ring

end Signal

section Separation
variable {V D L R : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
  [Fintype L] [Fintype R]

local notation "F" => GenericField V D

theorem same_side_generic_separation (v : L ⊕ R ↪ V)
    (hcard : Fintype.card (L ⊕ R) < Fintype.card (Sym2 (Option D)))
    (u w : Option D) (huw : u ≠ w)
    (a b : L ⊕ R) (hab : a ≠ b)
    (hside : (∃ i j, a = Sum.inl i ∧ b = Sum.inl j) ∨
      (∃ i j, a = Sum.inr i ∧ b = Sum.inr j)) :
    edgeRow (genericPosition (V := V) (D := D)) s(v a,v b) ∉
      Submodule.span F (genericRow (D := D) '' completeBipartite v) := by
  classical
  let p : V × D → F := genericPosition
  let Q := Submodule.span F (Set.range (fun r : L ⊕ R => quadricRow (fun i : D => p (v r,i))))
  let sign (b : V) : F := if b ∈ Set.range (leftEmbedding v) then 1 else -1
  have hl (i : L) : sign (v (Sum.inl i)) = 1 := by
    have hm : v (Sum.inl i) ∈ Set.range (leftEmbedding v) := ⟨i,rfl⟩
    change (if v (Sum.inl i) ∈ Set.range (leftEmbedding v) then (1 : F) else -1) = 1
    exact ite_eq_left hm
  have hr (j : R) : sign (v (Sum.inr j)) = -1 := by
    have hn : v (Sum.inr j) ∉ Set.range (leftEmbedding v) := by
      rintro ⟨i,hi⟩
      exact cross_ne v i j hi
    change (if v (Sum.inr j) ∈ Set.range (leftEmbedding v) then (1 : F) else -1) = -1
    exact ite_eq_right hn
  let S := signal p sign
  have hspan : Submodule.span F (genericRow (D := D) '' completeBipartite v) ≤ Q.comap S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨⟨i,j⟩,rfl⟩,rfl⟩
    change S (edgeRow p s(v (Sum.inl i),v (Sum.inr j))) ∈ Q
    rw [signal_cross p sign _ _ (hl i) (hr j)]
    exact Q.smul_mem _ (Q.sub_mem (Submodule.subset_span ⟨Sum.inl i,rfl⟩)
      (Submodule.subset_span ⟨Sum.inr j,rfl⟩))
  have hsgn : sign (v a) = sign (v b) ∧ sign (v a) ≠ 0 := by
    rcases hside with ⟨i,j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩
    · rw [hl, hl]
      exact ⟨rfl,one_ne_zero⟩
    · rw [hr, hr]
      exact ⟨rfl,neg_ne_zero.mpr one_ne_zero⟩
  intro hf
  have hh : S (edgeRow p s(v a,v b)) ∈ Q := hspan hf
  rw [signal_same p sign _ _ hsgn.1] at hh
  have h2 : (2 : F) ≠ 0 := by
    intro hz
    have hpoly : (2 : Poly V D) = 0 := IsFractionRing.injective (Poly V D) F (by
      simpa only [map_ofNat, map_zero] using hz)
    have hr := congrArg (MvPolynomial.constantCoeff : Poly V D →+* ℚ) hpoly
    change (MvPolynomial.constantCoeff : Poly V D →+* ℚ) 2 = 0 at hr
    rw [map_ofNat] at hr
    norm_num at hr
  have hz := Q.smul_mem (2 * sign (v a))⁻¹ hh
  rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero h2 hsgn.2), one_smul] at hz
  exact generic_secant_notMem_quadric_span v a b hab u w huw hcard hz

theorem Kss_same_side_generic_separation {V : Type*} [Fintype V] [DecidableEq V]
    (d : ℕ) (hd : 5 ≤ d) (v : Fin (d+2) ⊕ Fin (d+2) ↪ V)
    (a b : Fin (d+2) ⊕ Fin (d+2)) (hab : a ≠ b)
    (hside : (∃ i j, a = Sum.inl i ∧ b = Sum.inl j) ∨
      (∃ i j, a = Sum.inr i ∧ b = Sum.inr j)) :
    edgeRow (genericPosition (V := V) (D := Fin d)) s(v a,v b) ∉
      Submodule.span (GenericField V (Fin d))
        (genericRow (D := Fin d) '' completeBipartite v) := by
  let k : Fin d := ⟨0,by omega⟩
  apply same_side_generic_separation v _ none (some k) (by simp) a b hab hside
  have h := biclique_bound d (d+3) hd le_rfl
  unfold BipartiteBounds at h
  rw [Fintype.card_sum] at h ⊢
  simp only [Fintype.card_fin] at h ⊢
  omega

end Separation

#print axioms same_side_generic_separation
#print axioms Kss_same_side_generic_separation

end
end Rigidity369952
```

## ColumnCircuits.lean

```lean
import Separation

open scoped BigOperators

namespace Rigidity369952

noncomputable section

section SupportedRelations

variable {I J K : Type*} [Fintype I] [Field K]

theorem row_in_span_of_other_rows (x : I → J → K) (c : I → K)
    (hc : c ∈ relationSpace x) (e : I) (he : c e ≠ 0) :
    x e ∈ Submodule.span K (x '' {i | i ≠ e}) := by
  classical
  let S := Submodule.span K (x '' {i | i ≠ e})
  have hz : ∑ i, c i • x i = 0 := hc
  rw [Fintype.sum_eq_add_sum_subtype_ne _ e] at hz
  have hs : ∑ i : {i // i ≠ e}, c i.1 • x i.1 ∈ S :=
    S.sum_mem (fun i _ => S.smul_mem _ (Submodule.subset_span ⟨i.1,i.2,rfl⟩))
  have hv : c e • x e ∈ S := eq_neg_of_add_eq_zero_left hz ▸ S.neg_mem hs
  have hr := S.smul_mem (c e)⁻¹ hv
  rwa [smul_smul, inv_mul_cancel₀ he, one_smul] at hr

end SupportedRelations

section ColumnComplements

variable {L R V D : Type*} [Fintype L] [Fintype R] [Fintype D] [DecidableEq V]
  [DecidableEq D] [Nonempty L] [Nontrivial R]

local notation "F" => GenericField V D

def withoutColumn (v : L ⊕ R ↪ V) (j : R) : Set (Edge V) :=
  bipEdge v '' {e : L × R | e.2 ≠ j}

omit [Fintype L] [Fintype R] [Fintype D] [DecidableEq V] [DecidableEq D] [Nonempty L] [Nontrivial R] in
theorem mem_withoutColumn (v : L ⊕ R ↪ V) (e : L × R) (j : R) :
    bipEdge v e ∈ withoutColumn v j ↔ e.2 ≠ j := by
  constructor
  · rintro ⟨a,ha,he⟩
    exact (bipEdge_injective v he) ▸ ha
  · intro h
    exact ⟨e,h,rfl⟩

omit [Fintype D] [DecidableEq D] [Nonempty L] [Nontrivial R] in
theorem bipartite_dependent_of_supported_stress (v : L ⊕ R ↪ V) (E : Set (Edge V))
    (c : L × R → F) (hc : c ∈ stressSpace (D := D) v) (hn : c ≠ 0)
    (hs : ∀ e, bipEdge v e ∉ E → c e = 0) : ¬ GenericIndependent (D := D) E := by
  classical
  intro hI
  let P (e : L × R) := bipEdge v e ∈ E
  let f (e : {e // P e}) : E := ⟨bipEdge v e.1,e.2⟩
  have hf : Function.Injective f := fun _ _ eq => Subtype.ext (bipEdge_injective v (congrArg Subtype.val eq))
  have hi := hI.comp f hf
  exact hn (relation_zero_of_support (P := P) (crossRows (D := D) v) c hc hs hi)

theorem bipartite_column_complement_circuit (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 2) (j : R) :
    GenericCircuit D (withoutColumn v j) := by
  obtain ⟨μ,hμ⟩ := bipartite_stress_column_support v hq hL hR j
  obtain ⟨i₀⟩ := ‹Nonempty L›
  obtain ⟨k,hk⟩ := exists_ne j
  have hnon : μ.1 ≠ 0 := fun he => hk ((hμ (i₀,k)).mp (congrFun he (i₀,k)))
  constructor
  · refine bipartite_dependent_of_supported_stress v _ μ.1 μ.2 hnon (fun e he => (hμ e).mpr ?_)
    by_contra! hne
    exact he ((mem_withoutColumn v e j).mpr hne)
  · intro E hE
    have hsub : withoutColumn v j ⊆ completeBipartite v := fun _ ⟨e,_,he⟩ => ⟨e,he⟩
    apply generic_independent_bipartite_subset v (hE.le.trans hsub)
    intro c hc hs
    obtain ⟨e,hem,hen⟩ := Set.exists_of_ssubset hE
    obtain ⟨a,ham,rfl⟩ := hem
    have hj : bipEdge v (i₀,j) ∉ E := fun hm =>
      (mem_withoutColumn v (i₀,j) j).mp (hE.le hm) rfl
    have hne : a.2 ≠ (i₀,j).2 := ham
    have hzero := bipartite_two_column_zero v hq hL hR ⟨c,hc⟩ a (i₀,j) hne (hs a hen) (hs _ hj)
    exact congrArg Subtype.val hzero

theorem bipartite_delete_edge_span (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 2) (e : Edge V)
    (he : e ∈ completeBipartite v) :
    Submodule.span F (genericRow (D := D) '' (completeBipartite v \ {e})) =
      Submodule.span F (genericRow (D := D) '' completeBipartite v) := by
  obtain ⟨a,rfl⟩ := he
  obtain ⟨j,hj⟩ := exists_ne a.2
  obtain ⟨μ,hμ⟩ := bipartite_stress_column_support v hq hL hR j
  have hne : μ.1 a ≠ 0 := fun hz => hj ((hμ a).mp hz).symm
  have hm := row_in_span_of_other_rows (crossRows (D := D) v) μ.1 μ.2 a hne
  have hh : crossRows (D := D) v '' {i | i ≠ a} ⊆
      genericRow (D := D) '' (completeBipartite v \ {bipEdge v a}) := by
    rintro _ ⟨i,hi,rfl⟩
    exact ⟨bipEdge v i,⟨⟨i,rfl⟩,fun he => hi (bipEdge_injective v he)⟩,rfl⟩
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono Set.sdiff_subset)
  · apply Submodule.span_le.mpr
    rintro _ ⟨e,he,rfl⟩
    by_cases h : e = bipEdge v a
    · subst e
      exact Submodule.span_mono hh hm
    · exact Submodule.subset_span ⟨e,⟨he,h⟩,rfl⟩

theorem bipartite_double_circuit [Finite V] (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 2) :
    genericRank (D := D) (completeBipartite v) = (completeBipartite v).ncard - 2 ∧
      ∀ e ∈ completeBipartite v,
        genericRank (D := D) (completeBipartite v \ {e}) = genericRank (D := D) (completeBipartite v) := by
  have hc : (completeBipartite v).ncard = Fintype.card L * Fintype.card R := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr (Equiv.ofInjective (bipEdge v) (bipEdge_injective v)),
      Nat.card_eq_fintype_card, Fintype.card_prod]
  constructor
  · rw [hc]
    exact (bipartite_double_rank v hq hL hR).2
  · intro e he
    unfold genericRank
    rw [bipartite_delete_edge_span v hq hL hR e he]

end ColumnComplements

#print axioms row_in_span_of_other_rows
#print axioms bipartite_dependent_of_supported_stress
#print axioms bipartite_column_complement_circuit
#print axioms bipartite_delete_edge_span
#print axioms bipartite_double_circuit

end
end Rigidity369952
```

## Gadget.lean

```lean
import ColumnCircuits
import NativeRank

open scoped BigOperators

namespace Rigidity369952

noncomputable section

variable {L R V D : Type*} [Fintype L] [Fintype R] [Fintype D] [DecidableEq V]
  [DecidableEq D] [Nonempty L]

local notation "F" => GenericField V D

theorem square_stress_full_support (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 1)
    (μ : L × R → F) (hμ : μ ∈ stressSpace (D := D) v) (hn : μ ≠ 0) :
    ∀ e, μ e ≠ 0 := by
  obtain ⟨l,_,hl,hfac⟩ := stress_factorization v hq hL
  obtain ⟨c,hc,he⟩ := (hfac μ).mp hμ
  have hcn : c ≠ 0 := by
    intro h
    apply hn
    funext e
    change μ (e.1,e.2) = 0
    rw [he e.1 e.2, h]
    exact mul_zero _
  intro e
  change μ (e.1,e.2) ≠ 0
  rw [he e.1 e.2]
  exact mul_ne_zero (hl e.1)
    (affine_kernel_full_support (rightEmbedding v) hR c hc hcn e.2)

theorem square_seam_expansion [DecidableEq L] [DecidableEq R] (v : L ⊕ R ↪ V)
    (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 1)
    (e : L × R) :
    ∃ c : {a : L × R // a ≠ e} → F,
      (∑ a, c a • crossRows (D := D) v a.1) = crossRows v e ∧
      (∀ a, c a ≠ 0) ∧
      ∀ c', (∑ a, c' a • crossRows (D := D) v a.1) = crossRows v e → c' = c := by
  classical
  let x := crossRows (D := D) v
  have hdim := bipartite_stress_dim v hq hL (by omega)
  have hp : 0 < Module.finrank F (stressSpace (D := D) v) := by omega
  obtain ⟨μ,hμ,hne⟩ := relation_has_nonzero x hp
  have hμn := square_stress_full_support v hq hL hR μ hμ hne
  let c (a : {a : L × R // a ≠ e}) : F := -(μ e)⁻¹ * μ a.1
  have hc : (∑ a, c a • x a.1) = x e := by
    have hz : ∑ a, μ a • x a = 0 := hμ
    rw [Fintype.sum_eq_add_sum_subtype_ne _ e] at hz
    have hs := eq_neg_of_add_eq_zero_right hz
    have hsc : (∑ a, c a • x a.1) = -(μ e)⁻¹ •
        (∑ a : {a : L × R // a ≠ e}, μ a.1 • x a.1) := by
      simp only [Finset.smul_sum, smul_smul, c]
    rw [hsc, hs, smul_neg, neg_smul, neg_neg, smul_smul,
      inv_mul_cancel₀ (hμn e), one_smul]
  refine ⟨c,hc,fun a => mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (hμn e))) (hμn a.1),?_⟩
  intro c' hc'
  have hi : LinearIndependent F (fun a : {a : L × R // a ≠ e} => x a.1) := by
    apply independent_subtype_of_supported_zero x (fun a => a ≠ e)
    intro b hb hbs
    by_contra hbne
    exact square_stress_full_support v hq hL hR b hb hbne e (hbs e (not_not_intro rfl))
  have hz : ∑ a, (c' a - c a) • x a.1 = 0 := by
    change (∑ a, c' a • x a.1) = x e at hc'
    simp only [sub_smul, Finset.sum_sub_distrib, hc', hc, sub_self]
  funext a
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hi _ hz a)

omit [Nonempty L] in
theorem generic_Kss_seam_expansion {W : Type*} [DecidableEq W]
    (d : ℕ) (hd : 5 ≤ d) (v : Fin (d+2) ⊕ Fin (d+2) ↪ W)
    (e : Fin (d+2) × Fin (d+2)) :
    ∃ c : {a : Fin (d+2) × Fin (d+2) // a ≠ e} → GenericField W (Fin d),
      (∑ a, c a • crossRows (D := Fin d) v a.1) = crossRows v e ∧
      (∀ a, c a ≠ 0) ∧
      ∀ c', (∑ a, c' a • crossRows (D := Fin d) v a.1) = crossRows v e → c' = c :=
  square_seam_expansion v (biclique_bound d (d+2) hd (by omega))
    (by simp [Nat.add_assoc]) (by simp [Nat.add_assoc]) e

#print axioms square_stress_full_support
#print axioms square_seam_expansion
#print axioms generic_Kss_seam_expansion

end
end Rigidity369952
```

## Foundation.lean

```lean
import Gadget

namespace Rigidity369952

noncomputable section

theorem bipartite_circuits_iff_column_complements
    {L R V D : Type*} [Fintype L] [Fintype R] [Fintype D]
    [DecidableEq V] [DecidableEq D] [Nonempty L] [Nontrivial R]
    (v : L ⊕ R ↪ V) (hq : BipartiteBounds (L := L) (R := R) (D := D))
    (hL : Fintype.card L = Fintype.card (Option D) + 1)
    (hR : Fintype.card R = Fintype.card (Option D) + 2)
    (C : Set (Edge V)) (hC : C ⊆ completeBipartite v) :
    GenericCircuit D C ↔ ∃ j, C = withoutColumn v j := by
  classical
  constructor
  · intro h
    have hne : C ≠ completeBipartite v := by
      intro heq
      obtain ⟨i⟩ := ‹Nonempty L›
      obtain ⟨j⟩ := (inferInstance : Nonempty R)
      have hsub : withoutColumn v j ⊆ completeBipartite v := fun _ ⟨a,_,ha⟩ => ⟨a,ha⟩
      have hn : bipEdge v (i,j) ∉ withoutColumn v j := fun hm =>
        (mem_withoutColumn v (i,j) j).mp hm rfl
      have hproper : withoutColumn v j ⊂ C := by
        rw [heq]
        exact ssubset_of_subset_of_ne hsub (fun he => hn (he.symm ▸ ⟨(i,j),rfl⟩))
      exact (bipartite_column_complement_circuit v hq hL hR j).1 (h.2 _ hproper)
    have hproper : C ⊂ completeBipartite v := ssubset_of_subset_of_ne hC hne
    obtain ⟨_,⟨a,rfl⟩,ha⟩ := Set.exists_of_ssubset hproper
    have hs : ∃ μ : stressSpace (D := D) v,
        μ.1 ≠ 0 ∧ ∀ e, bipEdge v e ∉ C → μ.1 e = 0 := by
      by_contra! hn
      apply h.1
      apply generic_independent_bipartite_subset v hC
      intro c hc hs
      by_contra hne
      obtain ⟨e,he,hce⟩ := hn ⟨c,hc⟩ hne
      exact hce (hs e he)
    obtain ⟨μ,hμ,hsupp⟩ := hs
    have hsub : withoutColumn v a.2 ⊆ C := by
      rintro _ ⟨e,he,rfl⟩
      by_contra hn
      have hzero := bipartite_two_column_zero v hq hL hR μ e a he (hsupp e hn) (hsupp a ha)
      exact hμ (congrArg Subtype.val hzero)
    refine ⟨a.2, Eq.symm ?_⟩
    by_contra hn
    have hp := ssubset_of_subset_of_ne hsub hn
    exact (bipartite_column_complement_circuit v hq hL hR a.2).1 (h.2 _ hp)
  · rintro ⟨j,rfl⟩
    exact bipartite_column_complement_circuit v hq hL hR j

theorem generic_Kssplus1_double_circuit {V : Type*} [Finite V] [DecidableEq V] (d : ℕ)
    (hd : 5 ≤ d) (v : Fin (d+2) ⊕ Fin (d+3) ↪ V) :
    genericRank (D := Fin d) (completeBipartite v) = (completeBipartite v).ncard - 2 ∧
      ∀ e ∈ completeBipartite v,
        genericRank (D := Fin d) (completeBipartite v \ {e}) =
          genericRank (D := Fin d) (completeBipartite v) :=
  bipartite_double_circuit v (biclique_bound d (d+3) hd le_rfl)
    (by simp [Nat.add_assoc]) (by simp [Nat.add_assoc])

#print axioms bipartite_circuits_iff_column_complements
#print axioms generic_Kssplus1_double_circuit

end
end Rigidity369952
```

## NativeExistence.lean

```lean
import NativeRank
import Mathlib.Analysis.Real.Cardinality
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Algebra.MvPolynomial.Cardinal

open Cardinal

namespace Rigidity369952

theorem real_algebraicIndependent_exists (I : Type*) [Finite I] :
    ∃ p : I → ℝ, AlgebraicIndependent ℚ p := by
  obtain ⟨s,hs⟩ := exists_isTranscendenceBasis ℚ ℝ
  have hinf : Infinite s := by
    apply not_finite_iff_infinite.mp
    intro hfin
    let _ : Finite s := hfin
    let K := Algebra.adjoin ℚ (Set.range ((↑) : s → ℝ))
    have hm : #(MvPolynomial s ℚ) ≤ ℵ₀ := by
      apply MvPolynomial.cardinalMk_le_max.trans
      exact sup_le (sup_le (mk_le_aleph0_iff.mpr inferInstance)
        (mk_le_aleph0_iff.mpr inferInstance)) le_rfl
    have hk : #K ≤ ℵ₀ := (Cardinal.mk_congr hs.1.aevalEquiv.toEquiv).ge.trans hm
    let _ : Algebra.IsAlgebraic K ℝ := hs.isAlgebraic
    have hr : #ℝ ≤ ℵ₀ := (Algebra.IsAlgebraic.cardinalMk_le_max K ℝ).trans (max_le hk le_rfl)
    exact (aleph0_lt_mk_iff.mpr (inferInstance : Uncountable ℝ)).not_ge hr
  let _ : Infinite s := hinf
  let _ : Fintype I := Fintype.ofFinite I
  let e : I ↪ s := ((Fintype.equivFin I).toEmbedding.trans Fin.valEmbedding).trans
    (Infinite.natEmbedding s)
  exact ⟨Subtype.val ∘ e, hs.1.comp e e.injective⟩

theorem real_placement_with_all_generic_ranks {V D : Type*}
    [Finite V] [Finite D] [DecidableEq V] :
    ∃ p : V × D → ℝ, AlgebraicIndependent ℚ p ∧
      ∀ E : Set (Edge V), realRowRank p E = genericRank (D := D) E := by
  obtain ⟨p,hp⟩ := real_algebraicIndependent_exists (V × D)
  exact ⟨p,hp,real_rank_eq_genericRank p hp⟩

#print axioms real_algebraicIndependent_exists
#print axioms real_placement_with_all_generic_ranks

end Rigidity369952
```

## Signatures.lean

```lean
import Foundation
import NativeExistence

open Rigidity369952

#eval Lean.versionString

#check @Edge
#check @orderedRow
#check @edgeRow
#check @genericPosition
#check @genericRow
#check @genericRank
#check @GenericIndependent
#check @realEmbedding
#check @real_independent_iff
#check @real_rank_eq_genericRank
#check @real_placement_with_all_generic_ranks
#check @minor_ne_zero_of_specialization
#check @full_minor_of_independent
#check @independent_of_specialization
#check @generic_bary_independent
#check @generic_quadric_independent
#check @generic_secant_notMem_quadric_span
#check @force_iff_stress
#check @force_iff_affine
#check @stress_quadric_balance
#check @affine_kernel_finrank
#check @affine_kernel_full_support
#check @affine_kernel_two_zero
#check @stress_zero_marginals
#check @stress_factorization
#check @stress_space_equiv
#check @square_stress_full_support
#check @generic_Kss
#check @generic_Kssplus1
#check @generic_Kssplus1_double_circuit
#check @bipartite_stress_column_support
#check @bipartite_stress_column_classes
#check @bipartite_circuits_iff_column_complements
#check @Kss_same_side_generic_separation
#check @generic_two_vertex_seam
#check @generic_Kss_seam_expansion

#print axioms genericRank
#print axioms GenericIndependent
#print axioms real_placement_with_all_generic_ranks
#print axioms generic_bary_independent
#print axioms generic_quadric_independent
#print axioms independent_of_specialization
#print axioms stress_factorization
#print axioms stress_space_equiv
#print axioms generic_Kss
#print axioms generic_Kssplus1
#print axioms generic_Kssplus1_double_circuit
#print axioms bipartite_stress_column_classes
#print axioms bipartite_circuits_iff_column_complements
#print axioms Kss_same_side_generic_separation
#print axioms generic_two_vertex_seam
#print axioms generic_Kss_seam_expansion
```

## GlueLabels.lean

```lean
import Signatures

open scoped BigOperators

namespace Rigidity369952

noncomputable section

abbrev GlueS (d : ℕ) := Fin (d + 2)
abbrev GlueJ (d : ℕ) := Fin (d + 3)
abbrev GlueT (d : ℕ) := Fin (d + 1)
abbrev GlueV (d : ℕ) :=
  (GlueS d ⊕ (GlueJ d × GlueT d)) ⊕ (GlueJ d ⊕ (GlueJ d × GlueT d))

def glueBaseLabel (d : ℕ) : GlueS d ⊕ GlueJ d ↪ GlueV d where
  toFun := Sum.elim (fun i => .inl (.inl i)) (fun j => .inr (.inl j))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def glueLocalLeft {d : ℕ} (j : GlueJ d) : GlueS d → GlueS d ⊕ (GlueJ d × GlueT d) :=
  Fin.cases (.inl 0) (fun i => .inr (j,i))

def glueLocalRight {d : ℕ} (j : GlueJ d) : GlueS d → GlueJ d ⊕ (GlueJ d × GlueT d) :=
  Fin.cases (.inl j) (fun i => .inr (j,i))

theorem glueLocalLeft_injective {d : ℕ} (j : GlueJ d) :
    Function.Injective (glueLocalLeft j) := by
  intro a b
  refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b <;>
    simp [glueLocalLeft]

theorem glueLocalRight_injective {d : ℕ} (j : GlueJ d) :
    Function.Injective (glueLocalRight j) := by
  intro a b
  refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b <;>
    simp [glueLocalRight]

def glueLocalLabel {d : ℕ} (j : GlueJ d) : GlueS d ⊕ GlueS d ↪ GlueV d where
  toFun := Sum.map (glueLocalLeft j) (glueLocalRight j)
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [glueLocalLeft_injective j |>.eq_iff, glueLocalRight_injective j |>.eq_iff]

theorem glueV_card (d : ℕ) :
    Fintype.card (GlueV d) = 2*(d+2)^2 + 2*(d+2) - 1 := by
  simp [GlueV]
  apply Nat.eq_sub_of_add_eq
  ring

def glueEmbedding (d n : ℕ) (hn : 2*(d+2)^2 + 2*(d+2) - 1 ≤ n) : GlueV d ↪ Fin n :=
  embeddingOfCardLE (I := GlueV d) (J := Fin n) (by rw [glueV_card, Fintype.card_fin]; exact hn)

def glueBase {d n : ℕ} (emb : GlueV d ↪ Fin n) := (glueBaseLabel d).trans emb

def glueLocal {d n : ℕ} (emb : GlueV d ↪ Fin n) (j : GlueJ d) :=
  (glueLocalLabel j).trans emb

abbrev GlueLocalEdge (d : ℕ) := {e : GlueS d × GlueS d // e ≠ (0,0)}
abbrev GlueClass (d : ℕ) := GlueT d ⊕ GlueLocalEdge d
abbrev GlueIndex (d : ℕ) := GlueJ d × GlueClass d

def glueEdge {d n : ℕ} (emb : GlueV d ↪ Fin n) (e : GlueIndex d) : Edge (Fin n) :=
  match e.2 with
  | .inl i => bipEdge (glueBase emb) (i.succ,e.1)
  | .inr a => bipEdge (glueLocal emb e.1) a.1

def glueGround {d n : ℕ} (emb : GlueV d ↪ Fin n) : Set (Edge (Fin n)) :=
  Set.range (glueEdge emb)

@[simp] theorem glue_seam_left {d n : ℕ} (emb : GlueV d ↪ Fin n) (j : GlueJ d) :
    leftVertex (glueLocal emb j) 0 = leftVertex (glueBase emb) 0 := rfl

@[simp] theorem glue_seam_right {d n : ℕ} (emb : GlueV d ↪ Fin n) (j : GlueJ d) :
    rightVertex (glueLocal emb j) 0 = rightVertex (glueBase emb) j := rfl

@[simp] theorem glue_seam_edge {d n : ℕ} (emb : GlueV d ↪ Fin n) (j : GlueJ d) :
    bipEdge (glueLocal emb j) (0,0) = bipEdge (glueBase emb) (0,j) := rfl

def glueColumn {d : ℕ} (j : GlueJ d) (a : GlueClass d) :
    (GlueS d ⊕ (GlueJ d × GlueT d)) × (GlueJ d ⊕ (GlueJ d × GlueT d)) :=
  match a with
  | .inl i => (.inl i.succ, .inl j)
  | .inr p => (glueLocalLeft j p.1.1, glueLocalRight j p.1.2)

def glueRightCol {d : ℕ} : GlueJ d ⊕ (GlueJ d × GlueT d) → GlueJ d :=
  Sum.elim id Prod.fst

@[simp] theorem glueRightCol_local {d : ℕ} (j : GlueJ d) (i : GlueS d) :
    glueRightCol (glueLocalRight j i) = j := by
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem glueColumn_injective {d : ℕ} (j : GlueJ d) :
    Function.Injective (glueColumn j) := by
  intro a b h
  cases a with
  | inl i =>
    cases b with
    | inl k =>
      have hh := congrArg Prod.fst h
      simpa [glueColumn] using hh
    | inr p =>
      have hh : Sum.inl i.succ = glueLocalLeft j p.1.1 := congrArg Prod.fst h
      exfalso
      generalize p.1.1 = x at hh
      revert hh
      refine Fin.cases ?_ (fun a => ?_) x <;> simp [glueLocalLeft]
  | inr p =>
    cases b with
    | inl k =>
      have hh : glueLocalLeft j p.1.1 = Sum.inl k.succ := congrArg Prod.fst h
      exfalso
      generalize p.1.1 = x at hh
      revert hh
      refine Fin.cases ?_ (fun a => ?_) x <;> simp [glueLocalLeft, Ne.symm (Fin.succ_ne_zero k)]
    | inr q =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Prod.ext (glueLocalLeft_injective j (congrArg Prod.fst h))
        (glueLocalRight_injective j (congrArg Prod.snd h))

theorem glueColumn_right {d : ℕ} (j : GlueJ d) (a : GlueClass d) :
    glueRightCol (glueColumn j a).2 = j := by
  cases a with
  | inl => rfl
  | inr => exact glueRightCol_local _ _

theorem glueEdge_eq_bipEdge {d n : ℕ} (emb : GlueV d ↪ Fin n) (e : GlueIndex d) :
    glueEdge emb e = bipEdge emb (glueColumn e.1 e.2) := by
  rcases e with ⟨j,a⟩
  cases a <;> rfl

theorem glueEdge_injective {d n : ℕ} (emb : GlueV d ↪ Fin n) :
    Function.Injective (glueEdge emb) := by
  rintro ⟨j,a⟩ ⟨k,b⟩ h
  rw [glueEdge_eq_bipEdge, glueEdge_eq_bipEdge] at h
  have hcol := bipEdge_injective emb h
  have hjk : j = k := by
    simpa only [Function.comp_apply, glueColumn_right] using congrArg (glueRightCol ∘ Prod.snd) hcol
  subst k
  exact congrArg (Prod.mk j) (glueColumn_injective j hcol)

theorem glueLocalLeft_case {d : ℕ} (j : GlueJ d) (i : GlueS d) :
    glueLocalLeft j i = .inl 0 ∨ ∃ k, glueLocalLeft j i = .inr (j,k) := by
  refine Fin.cases (Or.inl rfl) (fun k => Or.inr ⟨k,rfl⟩) i

theorem glueLocalRight_case {d : ℕ} (j : GlueJ d) (i : GlueS d) :
    glueLocalRight j i = .inl j ∨ ∃ k, glueLocalRight j i = .inr (j,k) := by
  refine Fin.cases (Or.inl rfl) (fun k => Or.inr ⟨k,rfl⟩) i

def glueInternal {d : ℕ} (j : GlueJ d) : GlueV d → Prop
  | .inl (.inr (k,_)) | .inr (.inr (k,_)) => k = j
  | _ => False

theorem glueLocalLabel_cases {d : ℕ} (j : GlueJ d) (v : GlueS d ⊕ GlueS d) :
    glueLocalLabel j v = .inl (.inl 0) ∨ glueLocalLabel j v = .inr (.inl j) ∨
      glueInternal j (glueLocalLabel j v) := by
  rcases v with i | i
  · rcases glueLocalLeft_case j i with h | ⟨k,h⟩
    · exact Or.inl (congrArg Sum.inl h)
    · right; right
      change glueInternal j (Sum.inl (glueLocalLeft j i))
      rw [h]
      rfl
  · rcases glueLocalRight_case j i with h | ⟨k,h⟩
    · exact Or.inr (Or.inl (congrArg Sum.inr h))
    · right; right
      change glueInternal j (Sum.inr (glueLocalRight j i))
      rw [h]
      rfl

theorem glueInternal_unique {d : ℕ} {j k : GlueJ d} {v : GlueV d}
    (hj : glueInternal j v) (hk : glueInternal k v) : j = k := by
  rcases v with (i | ⟨l,i⟩) | (i | ⟨l,i⟩)
  · exact False.elim hj
  · exact hj.symm.trans hk
  · exact False.elim hj
  · exact hj.symm.trans hk

#print axioms glueV_card
#print axioms glueEdge_injective
#print axioms glueLocalLabel_cases
#print axioms glueInternal_unique
#print axioms glueEmbedding
#print axioms glue_seam_edge

end
end Rigidity369952
```

## GlueForce.lean

```lean
import GlueLabels

open scoped BigOperators

namespace Rigidity369952

noncomputable section

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)
local notation "W" => (Fin n × Fin d → F)

def glueRows (e : GlueIndex d) : W := genericRow (glueEdge emb e)

def glueRetainedForce (c : GlueIndex d → F) (j : GlueJ d) : W :=
  ∑ i : GlueT d, c (j,.inl i) • crossRows (glueBase emb) (i.succ,j)

def glueGadgetForce (c : GlueIndex d → F) (j : GlueJ d) : W :=
  ∑ a : GlueLocalEdge d, c (j,.inr a) • crossRows (glueLocal emb j) a.1

theorem glue_sum (c : GlueIndex d → F) :
    ∑ e, c e • glueRows emb e =
      ∑ j, (glueRetainedForce emb c j + glueGadgetForce emb c j) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => Fintype.sum_sum_type _

def glueAssemble (c : GlueIndex d → F) (z : GlueJ d → F)
    (e : GlueS d × GlueJ d) : F :=
  Fin.cases (z e.2) (fun i => c (e.2,.inl i)) e.1

theorem glue_assemble_sum (c : GlueIndex d → F) (z : GlueJ d → F) :
    ∑ e, glueAssemble c z e • crossRows (D := Fin d) (glueBase emb) e =
      ∑ j, (glueRetainedForce emb c j +
        z j • crossRows (D := Fin d) (glueBase emb) (0,j)) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_succ]
  exact add_comm _ _

theorem crossRows_zero_of_other_vertex {L R : Type*} (v : L ⊕ R ↪ Fin n)
    (a : L × R) (w : Fin n) (k : Fin d)
    (hl : w ≠ leftVertex v a.1) (hr : w ≠ rightVertex v a.2) :
    crossRows (D := Fin d) v a (w,k) = 0 := by
  change edgeRow genericPosition s(leftVertex v a.1,rightVertex v a.2) (w,k) = 0
  simp [edgeRow_pair, orderedRow, hl, hr]

def IsGlueInternal (j : GlueJ d) (w : Fin n) : Prop :=
  ∃ l, glueInternal j l ∧ emb l = w

theorem glue_internal_not_base {j : GlueJ d} {w : Fin n} (h : IsGlueInternal emb j w)
    (a : GlueS d ⊕ GlueJ d) : w ≠ glueBase emb a := by
  rcases h with ⟨l, hl, rfl⟩
  intro he
  have heq : l = glueBaseLabel d a := emb.injective he
  subst l
  cases a <;> exact hl

theorem glue_internal_unique {j l : GlueJ d} {w : Fin n}
    (hj : IsGlueInternal emb j w) (hl : IsGlueInternal emb l w) : j = l := by
  obtain ⟨u,hu,he⟩ := hj
  obtain ⟨v,hv,hf⟩ := hl
  have huv := emb.injective (he.trans hf.symm)
  subst v
  exact glueInternal_unique hu hv

theorem glue_local_vertex_cases (j : GlueJ d) (a : GlueS d ⊕ GlueS d) :
    glueLocal emb j a = leftVertex (glueBase emb) 0 ∨
      glueLocal emb j a = rightVertex (glueBase emb) j ∨
      IsGlueInternal emb j (glueLocal emb j a) := by
  rcases glueLocalLabel_cases j a with h | h | h
  · exact Or.inl (congrArg emb h)
  · exact Or.inr (Or.inl (congrArg emb h))
  · exact Or.inr (Or.inr ⟨_,h,rfl⟩)

theorem glue_gadget_force_zero (c : GlueIndex d → F) (j : GlueJ d) (w : Fin n)
    (k : Fin d) (hl : w ≠ leftVertex (glueBase emb) 0)
    (hr : w ≠ rightVertex (glueBase emb) j) (hi : ¬ IsGlueInternal emb j w) :
    glueGadgetForce emb c j (w,k) = 0 := by
  have hloc (a : GlueS d ⊕ GlueS d) : w ≠ glueLocal emb j a := by
    intro he
    rcases glue_local_vertex_cases emb j a with h | h | h
    · exact hl (he.trans h)
    · exact hr (he.trans h)
    · exact hi (he.symm ▸ h)
  simp only [glueGadgetForce, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a _
  rw [crossRows_zero_of_other_vertex (glueLocal emb j) a.1 w k
    (hloc (.inl a.1.1)) (hloc (.inr a.1.2)), mul_zero]

theorem glue_retained_force_zero (c : GlueIndex d → F) (j l : GlueJ d)
    (w : Fin n) (k : Fin d) (hw : IsGlueInternal emb j w) :
    glueRetainedForce emb c l (w,k) = 0 := by
  simp only [glueRetainedForce, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [crossRows_zero_of_other_vertex (glueBase emb) (i.succ,l) w k
    (glue_internal_not_base emb hw (.inl i.succ))
    (glue_internal_not_base emb hw (.inr l)), mul_zero]

theorem glue_force_at_internal (c : GlueIndex d → F) {j : GlueJ d}
    {w : Fin n} (hw : IsGlueInternal emb j w) (k : Fin d) :
    (∑ e, c e • glueRows emb e) (w,k) = glueGadgetForce emb c j (w,k) := by
  classical
  rw [glue_sum]
  simp only [Finset.sum_apply, Pi.add_apply, glue_retained_force_zero emb c j _ w k hw, zero_add]
  apply Finset.sum_eq_single j
  · intro l _ hlj
    exact glue_gadget_force_zero emb c l w k (glue_internal_not_base emb hw (.inl 0))
      (glue_internal_not_base emb hw (.inr l)) (fun hl => hlj (glue_internal_unique emb hl hw))
  · simp

theorem glue_gadget_recompress (hd : 5 ≤ d) (c : GlueIndex d → F) (j : GlueJ d)
    (hz : ∀ w, IsGlueInternal emb j w → ∀ k, (∑ e, c e • glueRows emb e) (w,k) = 0) :
    ∃ z : F, glueGadgetForce emb c j = z • crossRows (D := Fin d) (glueBase emb) (0,j) := by
  let k : Fin d := ⟨0,by omega⟩
  let a := leftVertex (glueBase emb) 0
  let b := rightVertex (glueBase emb) j
  apply generic_two_vertex_seam (completeBipartite (glueLocal emb j)) a b
    (cross_ne (glueBase emb) 0 j) k
  · exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨bipEdge (glueLocal emb j) p.1, ⟨p.1,rfl⟩, rfl⟩)
  · intro w i hwa hwb
    by_cases hi : IsGlueInternal emb j w
    · exact (glue_force_at_internal emb c hi i).symm.trans (hz w hi i)
    · exact glue_gadget_force_zero emb c j w i hwa hwb hi

#print axioms glue_sum
#print axioms glue_assemble_sum
#print axioms glue_force_at_internal
#print axioms glue_gadget_recompress

end
end Rigidity369952
```

## GlueStress.lean

```lean
import GlueForce

open scoped BigOperators

namespace Rigidity369952

noncomputable section

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)

structure GlueSeams where
  weights : GlueJ d → GlueLocalEdge d → F
  expands : ∀ j, (∑ a, weights j a • crossRows (D := Fin d) (glueLocal emb j) a.1) =
    crossRows (D := Fin d) (glueBase emb) (0,j)
  nonzero : ∀ j a, weights j a ≠ 0
  unique : ∀ j c, (∑ a : GlueLocalEdge d, c a • crossRows (D := Fin d) (glueLocal emb j) a.1) =
    crossRows (D := Fin d) (glueBase emb) (0,j) → c = weights j

def glueSeams (hd : 5 ≤ d) : GlueSeams emb := by
  have h (j : GlueJ d) := generic_Kss_seam_expansion d hd (glueLocal emb j) (0,0)
  simp only [crossRows, glue_seam_edge] at h
  exact ⟨fun j => (h j).choose, fun j => (h j).choose_spec.1,
    fun j => (h j).choose_spec.2.1, fun j => (h j).choose_spec.2.2⟩

variable {emb} (β : GlueSeams emb)

theorem glue_gadget_factor (c : GlueIndex d → F) (j : GlueJ d) (z : F)
    (hz : glueGadgetForce emb c j = z • crossRows (D := Fin d) (glueBase emb) (0,j))
    (a : GlueLocalEdge d) : c (j,.inr a) = z * β.weights j a := by
  let x := crossRows (D := Fin d) (glueLocal emb j)
  let b : GlueLocalEdge d → F := fun a => c (j,.inr a) + (1-z) * β.weights j a
  have hb : ∑ a : GlueLocalEdge d, b a • x a.1 =
      crossRows (D := Fin d) (glueBase emb) (0,j) := by
    simp only [b, add_smul, Finset.sum_add_distrib, ← smul_smul, ← Finset.smul_sum, x]
    change glueGadgetForce emb c j + (1-z) •
        (∑ a, β.weights j a • crossRows (D := Fin d) (glueLocal emb j) a.1) = _
    rw [hz, β.expands, ← add_smul, add_sub_cancel, one_smul]
  have hh := congrFun (β.unique j b hb) a
  dsimp [b] at hh
  linear_combination hh

def glueExpand (b : GlueS d × GlueJ d → F) : GlueIndex d → F :=
  fun e => match e.2 with
    | .inl i => b (i.succ,e.1)
    | .inr a => b (0,e.1) * β.weights e.1 a

theorem glue_expand_sums (b : GlueS d × GlueJ d → F) :
    ∑ e, glueExpand β b e • glueRows emb e =
      ∑ e, b e • crossRows (D := Fin d) (glueBase emb) e := by
  rw [glue_sum, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_succ]
  have hg : glueGadgetForce emb (glueExpand β b) j =
      b (0,j) • crossRows (D := Fin d) (glueBase emb) (0,j) := by
    simp only [glueGadgetForce, glueExpand, ← smul_smul, ← Finset.smul_sum, β.expands]
  rw [hg, add_comm]
  rfl

def glueStressMap : stressSpace (D := Fin d) (glueBase emb) →ₗ[F]
    relationSpace (glueRows emb) where
  toFun b := ⟨glueExpand β b, by
    change ∑ e, glueExpand β b e • glueRows emb e = 0
    rw [glue_expand_sums]
    exact b.property⟩
  map_add' b c := by
    apply Subtype.ext
    funext e
    rcases e with ⟨j,i | a⟩
    · rfl
    · exact add_mul _ _ _
  map_smul' z b := by
    apply Subtype.ext
    funext e
    rcases e with ⟨j,i | a⟩
    · rfl
    · exact mul_assoc _ _ _

theorem glue_stress_injective : Function.Injective (glueStressMap β) := by
  intro b c h
  apply Subtype.ext
  funext e
  obtain ⟨i,j⟩ := e
  have hh := congrArg Subtype.val h
  change glueExpand β b.1 = glueExpand β c.1 at hh
  refine Fin.cases ?_ (fun k => ?_) i
  · let a : GlueLocalEdge d := ⟨(Fin.succ 0,0),by simp⟩
    have he := congrFun hh (j,.inr a)
    exact mul_right_cancel₀ (β.nonzero j a) he
  · exact congrFun hh (j,.inl k)

theorem glue_stress_surjective (hd : 5 ≤ d) : Function.Surjective (glueStressMap β) := by
  intro c
  have hc : ∑ e, c.1 e • glueRows emb e = 0 := c.2
  have hrec (j : GlueJ d) := glue_gadget_recompress emb hd c.1 j
    (fun w _ k => by rw [hc]; rfl)
  choose z hz using hrec
  let b := glueAssemble c.1 z
  have hb : b ∈ stressSpace (D := Fin d) (glueBase emb) := by
    change ∑ e, b e • crossRows (D := Fin d) (glueBase emb) e = 0
    rw [glue_assemble_sum]
    simpa only [glue_sum, hz] using hc
  refine ⟨⟨b,hb⟩,Subtype.ext ?_⟩
  funext e
  rcases e with ⟨j,i | a⟩
  · rfl
  · exact (glue_gadget_factor β c.1 j (z j) (hz j) a).symm

def glueStressEquiv (hd : 5 ≤ d) : stressSpace (D := Fin d) (glueBase emb) ≃ₗ[F]
    relationSpace (glueRows emb) :=
  LinearEquiv.ofBijective (glueStressMap β) ⟨glue_stress_injective β,glue_stress_surjective β hd⟩

#print axioms glueSeams
#print axioms glue_gadget_factor
#print axioms glueStressEquiv

end
end Rigidity369952
```

## GlueParameters.lean

```lean
import GlueStress

open scoped BigOperators

namespace Rigidity369952

noncomputable section

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)

abbrev GlueParameters := relationSpace (affineRow (D := Fin d) (rightEmbedding (glueBase emb)))

theorem glue_parameter_dim : Module.finrank F (GlueParameters emb) = 2 := by
  rw [affine_kernel_finrank]
  · simp
  · simp

theorem glue_parameter_two_zero (c : GlueParameters emb) {j k : GlueJ d}
    (hjk : j ≠ k) (hj : c.1 j = 0) (hk : c.1 k = 0) : c = 0 :=
  Subtype.ext (affine_kernel_two_zero (rightEmbedding (glueBase emb))
    (by simp [Nat.add_assoc]) c.1 c.2 hjk hj hk)

theorem glue_coordinate_surjective (j : GlueJ d) : Function.Surjective (coordinate (GlueParameters emb) j) := by
  have hn : ∃ c : GlueParameters emb, c.1 j ≠ 0 := by
    by_contra! hz
    obtain ⟨k,hkj⟩ := exists_ne j
    have hi : Function.Injective (coordinate (GlueParameters emb) k) := by
      intro a b hab
      have he : coordinate (GlueParameters emb) k (a-b) = 0 := by rw [map_sub,hab,sub_self]
      exact sub_eq_zero.mp (glue_parameter_two_zero emb (a-b) hkj.symm (hz _) he)
    have hf := LinearMap.finrank_le_finrank_of_injective hi
    rw [glue_parameter_dim, Module.finrank_self] at hf
    omega
  obtain ⟨c,hc⟩ := hn
  intro z
  exact ⟨(z / c.1 j) • c, div_mul_cancel₀ _ hc⟩

theorem glue_coordinate_kernel_rank (j : GlueJ d) :
    Module.finrank F (LinearMap.ker (coordinate (GlueParameters emb) j)) = 1 :=
  coordinate_kernel_finrank _ (glue_parameter_dim emb)
    (fun c _ _ h => glue_parameter_two_zero emb c h) j

private theorem glue_base_factor (hd : 5 ≤ d) :
    ∃ l : GlueS d → F, l ∈ relationSpace (affineRow (D := Fin d) (leftEmbedding (glueBase emb))) ∧
      (∀ i, l i ≠ 0) ∧ ∀ b : GlueS d × GlueJ d → F,
        b ∈ stressSpace (D := Fin d) (glueBase emb) ↔
          ∃ c : GlueJ d → F, c ∈ GlueParameters emb ∧ ∀ i j, b (i,j) = l i * c j :=
  stress_factorization (D := Fin d) (glueBase emb) (biclique_bound d (d+3) hd le_rfl)
    (by simp [Nat.add_assoc])

def glueLambda (hd : 5 ≤ d) : GlueS d → F := (glue_base_factor emb hd).choose

theorem glueLambda_rel (hd : 5 ≤ d) :
    glueLambda emb hd ∈ relationSpace (affineRow (D := Fin d) (leftEmbedding (glueBase emb))) :=
  (glue_base_factor emb hd).choose_spec.1

theorem glueLambda_ne (hd : 5 ≤ d) (i : GlueS d) : glueLambda emb hd i ≠ 0 :=
  (glue_base_factor emb hd).choose_spec.2.1 i

def glueBaseMap (hd : 5 ≤ d) : GlueParameters emb →ₗ[F] stressSpace (D := Fin d) (glueBase emb) where
  toFun c := ⟨fun e => glueLambda emb hd e.1 * c.1 e.2,
    ((glue_base_factor emb hd).choose_spec.2.2 _).mpr ⟨c.1,c.2,fun _ _ => rfl⟩⟩
  map_add' _ _ := Subtype.ext (funext fun _ => mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => mul_left_comm _ _ _)

def glueBaseEquiv (hd : 5 ≤ d) : GlueParameters emb ≃ₗ[F] stressSpace (D := Fin d) (glueBase emb) :=
  LinearEquiv.ofBijective (glueBaseMap emb hd) ⟨by
    intro a b h
    exact Subtype.ext (funext fun j =>
      mul_left_cancel₀ (glueLambda_ne emb hd 0) (congrFun (congrArg Subtype.val h) (0,j))),
    by
      intro μ
      obtain ⟨c,hc,he⟩ := ((glue_base_factor emb hd).choose_spec.2.2 _).mp μ.2
      exact ⟨⟨c,hc⟩, Subtype.ext (funext fun e => (he e.1 e.2).symm)⟩⟩

def glueParameterEquiv (hd : 5 ≤ d) : GlueParameters emb ≃ₗ[F] relationSpace (glueRows emb) :=
  (glueBaseEquiv emb hd).trans (glueStressEquiv (glueSeams emb hd) hd)

def glueWeight (hd : 5 ≤ d) (e : GlueIndex d) : F :=
  match e.2 with
  | .inl i => glueLambda emb hd i.succ
  | .inr a => glueLambda emb hd 0 * (glueSeams emb hd).weights e.1 a

theorem glueWeight_ne (hd : 5 ≤ d) (e : GlueIndex d) : glueWeight emb hd e ≠ 0 := by
  rcases e with ⟨j,i | a⟩
  · exact glueLambda_ne emb hd i.succ
  · exact mul_ne_zero (glueLambda_ne emb hd 0) ((glueSeams emb hd).nonzero j a)

theorem glue_factor (hd : 5 ≤ d) (c : GlueParameters emb) (e : GlueIndex d) :
    (glueParameterEquiv emb hd c).1 e = glueWeight emb hd e * c.1 e.1 := by
  rcases e with ⟨j,i | a⟩
  · rfl
  · change (glueLambda emb hd 0 * c.1 j) * (glueSeams emb hd).weights j a =
      (glueLambda emb hd 0 * (glueSeams emb hd).weights j a) * c.1 j
    exact mul_right_comm _ _ _

theorem glue_stress_zero_iff (hd : 5 ≤ d) (c : GlueParameters emb) (e : GlueIndex d) :
    (glueParameterEquiv emb hd c).1 e = 0 ↔ c.1 e.1 = 0 := by
  rw [glue_factor]
  simp only [mul_eq_zero, glueWeight_ne emb hd e, false_or]

theorem glue_stress_two_class_zero (hd : 5 ≤ d) (c : relationSpace (glueRows emb))
    (e f : GlueIndex d) (hef : e.1 ≠ f.1) (he : c.1 e = 0) (hf : c.1 f = 0) : c = 0 := by
  obtain ⟨a,rfl⟩ := (glueParameterEquiv emb hd).surjective c
  have ha := glue_parameter_two_zero emb a hef ((glue_stress_zero_iff emb hd a e).mp he)
    ((glue_stress_zero_iff emb hd a f).mp hf)
  rw [ha, map_zero]

#print axioms glue_parameter_dim
#print axioms glue_coordinate_surjective
#print axioms glue_coordinate_kernel_rank
#print axioms glueLambda_rel
#print axioms glueParameterEquiv
#print axioms glueWeight_ne
#print axioms glue_factor
#print axioms glue_stress_two_class_zero

end
end Rigidity369952
```

## GlueRanks.lean

```lean
import GlueParameters

open scoped BigOperators

namespace Rigidity369952

noncomputable section

section Restriction
variable {I A K : Type*} [Field K]
variable (x : I → A → K) (P : I → Prop) [DecidablePred P]

def zeroExtend (b : {e // P e} → K) (e : I) : K := if h : P e then b ⟨e,h⟩ else 0

@[simp] theorem zeroExtend_on (b : {e // P e} → K) (e : {e // P e}) :
    zeroExtend P b e.1 = b e := dite_eq_left e.2

@[simp] theorem zeroExtend_off (b : {e // P e} → K) {e : I} (he : ¬ P e) :
    zeroExtend P b e = 0 := dite_eq_right he

variable [Fintype I]

theorem supported_sum (b : I → K) (hb : ∀ e, ¬ P e → b e = 0) :
    (∑ e : {e // P e}, b e.1 • x e.1) = ∑ e, b e • x e := by
  classical
  rw [← Finset.subtype_univ P, Finset.sum_subtype_eq_sum_filter (fun e => b e • x e),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : P e <;> simp [he, hb]

def supportedRelations : Submodule K (relationSpace x) where
  carrier := {b | ∀ e, ¬ P e → b.1 e = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb e he => by
    change a.1 e + b.1 e = (0 : K)
    rw [ha e he,hb e he,add_zero]
  smul_mem' := fun a _ hb e he => by
    change a * _ = (0 : K)
    rw [hb e he,mul_zero]

def restrictStressEquiv :
    supportedRelations x P ≃ₗ[K] relationSpace (fun e : {e // P e} => x e.1) where
  toFun b := ⟨fun e => b.1.1 e.1, by
    change ∑ e : {e // P e}, b.1.1 e.1 • x e.1 = 0
    rw [supported_sum x P _ b.2]
    exact b.1.2⟩
  invFun b := ⟨⟨zeroExtend P b.1, by
    change ∑ e, zeroExtend P b.1 e • x e = 0
    rw [← supported_sum x P _ (fun _ he => zeroExtend_off P _ he)]
    have hb : ∑ e : {e // P e}, b.1 e • x e.1 = 0 := b.2
    simpa only [zeroExtend_on] using hb⟩, fun _ he => zeroExtend_off P _ he⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    funext e
    by_cases he : P e
    · exact dite_eq_left he
    · exact (dite_eq_right he).trans ((b.2 e he).symm)
  right_inv b := Subtype.ext (funext (zeroExtend_on P b.1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Restriction

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)

def glueSubset (P : GlueIndex d → Prop) : Set (Edge (Fin n)) :=
  glueEdge emb '' {e | P e}

theorem glue_mem_subset (P : GlueIndex d → Prop) (e : GlueIndex d) :
    glueEdge emb e ∈ glueSubset emb P ↔ P e := by
  constructor
  · rintro ⟨a,ha,he⟩
    exact (glueEdge_injective emb he) ▸ ha
  · exact fun pe => ⟨e,pe,rfl⟩

def glueSubsetEquiv (P : GlueIndex d → Prop) : {e // P e} ≃ glueSubset emb P :=
  Equiv.ofBijective (fun e => ⟨glueEdge emb e.1,⟨e.1,e.2,rfl⟩⟩) ⟨
    fun _ _ h => Subtype.ext (glueEdge_injective emb (congrArg Subtype.val h)),
    fun ⟨_,e,he,rfl⟩ => ⟨⟨e,he⟩,rfl⟩⟩

def glueAllowedParameters (P : GlueIndex d → Prop) : Submodule F (GlueParameters emb) where
  carrier := {c | ∀ e, ¬ P e → c.1 e.1 = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb e he => by
    change a.1 e.1 + b.1 e.1 = (0 : F)
    rw [ha e he,hb e he,add_zero]
  smul_mem' := fun a _ hb e he => by
    change a * _ = (0 : F)
    rw [hb e he,mul_zero]

def glueRestrictedParameters (hd : 5 ≤ d) (P : GlueIndex d → Prop) [DecidablePred P] :
    glueAllowedParameters emb P ≃ₗ[F]
      relationSpace (fun e : {e // P e} => glueRows emb e.1) := by
  let E := glueParameterEquiv emb hd
  let f : glueAllowedParameters emb P →ₗ[F] supportedRelations (glueRows emb) P :=
    ((E.toLinearMap).comp (glueAllowedParameters emb P).subtype).codRestrict _ <| by
      intro c e he
      exact (glue_stress_zero_iff emb hd c.1 e).mpr (c.2 e he)
  refine (LinearEquiv.ofBijective f ⟨?_,?_⟩).trans (restrictStressEquiv _ P)
  · intro a b h
    have he : E a.1 = E b.1 := congrArg (fun t : supportedRelations (glueRows emb) P => t.1) h
    exact Subtype.ext (E.injective he)
  · intro b
    obtain ⟨c,hc⟩ := E.surjective b.1
    refine ⟨⟨c,?_⟩,Subtype.ext hc⟩
    intro e he
    apply (glue_stress_zero_iff emb hd c e).mp
    rw [show glueParameterEquiv emb hd c = b.1 from hc]
    exact b.2 e he

theorem glue_subset_rank_add (hd : 5 ≤ d) (P : GlueIndex d → Prop) [DecidablePred P] :
    genericRank (D := Fin d) (glueSubset emb P) +
      Module.finrank F (glueAllowedParameters emb P) = Fintype.card {e // P e} := by
  let r := fun e : {e // P e} => glueRows emb e.1
  have h := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination F r)
  rw [Fintype.range_linearCombination, Module.finrank_fintype_fun_eq_card,
    ← (glueRestrictedParameters emb hd P).finrank_eq] at h
  have hr : Set.range r = genericRow '' glueSubset emb P := by
    ext z
    exact ⟨fun ⟨⟨e,he⟩,hz⟩ => ⟨glueEdge emb e,⟨e,he,rfl⟩,hz⟩,
      fun ⟨_,⟨e,he,rfl⟩,hz⟩ => ⟨⟨e,he⟩,hz⟩⟩
  rw [hr] at h
  exact h

def glueDelete (S : Finset (GlueIndex d)) : Set (Edge (Fin n)) :=
  glueSubset emb (· ∉ S)

theorem glue_delete_eq (S : Finset (GlueIndex d)) :
    glueDelete emb S = glueGround emb \ glueEdge emb '' (↑S : Set (GlueIndex d)) := by
  ext a
  constructor
  · rintro ⟨e,he,rfl⟩
    exact ⟨⟨e,rfl⟩,fun ⟨f,hf,h⟩ => he ((glueEdge_injective emb h) ▸ hf)⟩
  · rintro ⟨⟨e,rfl⟩,he⟩
    exact ⟨e,fun hm => he ⟨e,hm,rfl⟩,rfl⟩

theorem glue_class_card (d : ℕ) :
    Fintype.card (GlueClass d) = (d+2)^2 + (d+2) - 2 := by
  have h := Fintype.card_subtype_compl (fun a : GlueS d × GlueS d => a = (0,0))
  rw [Fintype.card_subtype_eq, Fintype.card_prod, Fintype.card_fin] at h
  change Fintype.card (GlueLocalEdge d) = (d+2)*(d+2)-1 at h
  rw [Fintype.card_sum, Fintype.card_fin, h, pow_two]
  have hpos : 0 < (d+2)*(d+2) := by positivity
  omega

theorem glue_ground_rank (hd : 5 ≤ d) :
    genericRank (D := Fin d) (glueGround emb) =
      (d+3) * ((d+2)^2 + (d+2) - 2) - 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination F (glueRows emb))
  rw [Fintype.range_linearCombination, Module.finrank_fintype_fun_eq_card,
    ← (glueParameterEquiv emb hd).finrank_eq, glue_parameter_dim,
    Fintype.card_prod, Fintype.card_fin, glue_class_card] at h
  have hr : Set.range (glueRows emb) = genericRow '' glueGround emb := by
    rw [glueGround, ← Set.range_comp]
    rfl
  rw [hr] at h
  exact Nat.eq_sub_of_add_eq h

theorem glue_allowed_same (P : GlueIndex d → Prop) (e : GlueIndex d) (he : ¬ P e)
    (hs : ∀ f, ¬ P f → f.1 = e.1) :
    glueAllowedParameters emb P = LinearMap.ker (coordinate (GlueParameters emb) e.1) := by
  ext a
  change (∀ f, ¬ P f → a.1 f.1 = 0) ↔ a.1 e.1 = 0
  exact ⟨fun h => h e he, fun h f hf => (hs f hf).symm ▸ h⟩

theorem glue_allowed_cross (P : GlueIndex d → Prop) (e f : GlueIndex d)
    (he : ¬ P e) (hf : ¬ P f) (hef : e.1 ≠ f.1) : glueAllowedParameters emb P = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have hz := glue_parameter_two_zero emb a hef (ha e he) (ha f hf)
  rw [hz]
  exact Submodule.zero_mem _

theorem glue_delete_same_rank (hd : 5 ≤ d) (S : Finset (GlueIndex d))
    (e : GlueIndex d) (he : e ∈ S) (hs : ∀ f ∈ S, f.1 = e.1) :
    genericRank (D := Fin d) (glueDelete emb S) =
      (d+3) * ((d+2)^2 + (d+2) - 2) - S.card - 1 := by
  classical
  have h := glue_subset_rank_add emb hd (· ∉ S)
  rw [glue_allowed_same emb (· ∉ S) e (not_not_intro he)
    (fun f hf => hs f (not_not.mp hf)), glue_coordinate_kernel_rank,
    Fintype.card_subtype_compl (· ∈ S), Fintype.card_coe,
    Fintype.card_prod, Fintype.card_fin, glue_class_card] at h
  exact Nat.eq_sub_of_add_eq h

theorem glue_delete_cross_rank (hd : 5 ≤ d) (S : Finset (GlueIndex d))
    (e f : GlueIndex d) (he : e ∈ S) (hf : f ∈ S) (hef : e.1 ≠ f.1) :
    genericRank (D := Fin d) (glueDelete emb S) = (d+3) * ((d+2)^2 + (d+2) - 2) - S.card := by
  classical
  have h := glue_subset_rank_add emb hd (· ∉ S)
  rw [glue_allowed_cross emb (· ∉ S) e f (not_not_intro he) (not_not_intro hf) hef,
    finrank_bot, add_zero, Fintype.card_subtype_compl (· ∈ S), Fintype.card_coe,
    Fintype.card_prod, Fintype.card_fin, glue_class_card] at h
  exact h

def glueClassSet (j : GlueJ d) : Set (Edge (Fin n)) :=
  glueSubset emb (fun e => e.1 = j)

def glueClassEquiv (j : GlueJ d) : {e : GlueIndex d // e.1 = j} ≃ GlueClass d where
  toFun e := e.1.2
  invFun a := ⟨(j,a),rfl⟩
  left_inv := by rintro ⟨⟨k,a⟩,h⟩; cases h; rfl
  right_inv := fun _ => rfl

theorem glue_class_rank (hd : 5 ≤ d) (j : GlueJ d) :
    genericRank (D := Fin d) (glueClassSet emb j) = (d+2)^2 + (d+2) - 2 := by
  let e : GlueIndex d := (j+1,.inl 0)
  let f : GlueIndex d := (j+1+1,.inl 0)
  have h1 : (1 : GlueJ d) ≠ 0 := by intro h; have hv := congrArg Fin.val h; change 1 = 0 at hv; omega
  have he : ¬ e.1 = j := fun h => h1 (add_left_cancel (b := 1) (c := 0) (h.trans (add_zero j).symm))
  have hef : e.1 ≠ f.1 := fun h => h1 (add_left_cancel
    (a := j+1) (b := 1) (c := 0) (h.symm.trans (add_zero (j+1)).symm))
  have hf : ¬ f.1 = j := by
    intro h
    have hh : (2 : GlueJ d) = 0 := add_left_cancel
      ((add_assoc j 1 1).symm.trans (h.trans (add_zero j).symm))
    have hval := congrArg Fin.val hh
    have htwo : (2 : ℕ) < d+3 := by omega
    simp [Nat.mod_eq_of_lt htwo] at hval
  have h := glue_subset_rank_add emb hd (fun e => e.1 = j)
  rw [glue_allowed_cross emb _ e f he hf hef, finrank_bot, add_zero,
    Fintype.card_congr (glueClassEquiv j), glue_class_card] at h
  exact h

theorem glue_class_complement_rank (hd : 5 ≤ d) (j : GlueJ d) :
    genericRank (D := Fin d) (glueGround emb \ glueClassSet emb j) =
      (d+2) * ((d+2)^2 + (d+2) - 2) - 1 := by
  let S : Finset (GlueIndex d) := Finset.univ.filter (fun e => e.1 = j)
  have hS : (↑S : Set (GlueIndex d)) = {e | e.1 = j} := by ext e; simp [S]
  have hcard : S.card = (d+2)^2 + (d+2) - 2 := by
    rw [← Fintype.card_subtype (fun e : GlueIndex d => e.1 = j),
      Fintype.card_congr (glueClassEquiv j), glue_class_card]
  have ho : (j,.inl 0) ∈ S := by simp [S]
  have h := glue_delete_same_rank emb hd S (j,.inl 0) ho
    (fun f hf => Finset.mem_filter.mp hf |>.2)
  rw [glue_delete_eq, hS, ← glueSubset, ← glueClassSet, hcard] at h
  have he (L : ℕ) : (d+3)*L-L-1 = (d+2)*L-1 := by
    change ((d+2)+1)*L-L-1 = _
    rw [Nat.add_mul (d+2) 1 L, one_mul, Nat.add_sub_cancel]
  exact h.trans (he _)

#print axioms glueClassEquiv
#print axioms glue_class_rank
#print axioms glue_class_complement_rank
#print axioms glueSubsetEquiv
#print axioms glue_delete_eq
#print axioms glueRestrictedParameters
#print axioms glue_class_card
#print axioms glue_ground_rank
#print axioms glue_delete_same_rank
#print axioms glue_delete_cross_rank

end
end Rigidity369952
```

## GluePairs.lean

```lean
import GlueRanks

open scoped BigOperators

namespace Rigidity369952

noncomputable section

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)
local notation "W" => (Fin n × Fin d → F)

abbrev GluePairKind (d : ℕ) := GlueT d ⊕ (GlueS d × Fin ((d+1)/2))
abbrev GluePairName (d : ℕ) := GlueJ d × GluePairKind d

def glueHalfEquiv (hodd : Odd d) : (Fin ((d+1)/2) × Fin 2) ≃ GlueT d :=
  finProdFinEquiv.trans (finCongr (by obtain ⟨k,hk⟩ := hodd; omega))

def glueCrossGadget (i : GlueT d) : GlueLocalEdge d :=
  ⟨(i.succ,0),by simp⟩

def glueExtraGadget (hodd : Odd d) (i : GlueS d) (r : Fin ((d+1)/2)) (b : Fin 2) :
    GlueLocalEdge d :=
  ⟨(i,(glueHalfEquiv hodd (r,b)).succ),by simp⟩

def gluePairClass (hodd : Odd d) (t : GluePairKind d × Fin 2) : GlueClass d :=
  match t.1 with
  | .inl i => if t.2 = 0 then .inl i else .inr (glueCrossGadget i)
  | .inr (i,r) => .inr (glueExtraGadget hodd i r t.2)

theorem gluePairClass_injective (hodd : Odd d) : Function.Injective (gluePairClass hodd) := by
  rintro ⟨i | ⟨i,r⟩,b⟩ ⟨j | ⟨j,s⟩,c⟩
  · fin_cases b <;> fin_cases c <;> simp [gluePairClass, glueCrossGadget, Subtype.ext_iff]
  · fin_cases b <;> simp [gluePairClass, glueCrossGadget, glueExtraGadget, Subtype.ext_iff,
      Ne.symm (Fin.succ_ne_zero _)]
  · fin_cases c <;> simp [gluePairClass, glueCrossGadget, glueExtraGadget, Subtype.ext_iff]
  · intro h
    have he : glueExtraGadget hodd i r b = glueExtraGadget hodd j s c := Sum.inr.inj h
    have hi := congrArg (fun a : GlueLocalEdge d => a.1.1) he
    have hz := congrArg (fun a : GlueLocalEdge d => a.1.2) he
    have hh := (glueHalfEquiv hodd).injective (Fin.succ_injective _ hz)
    rcases Prod.ext_iff.mp hh with ⟨rfl,rfl⟩
    cases hi
    rfl

theorem gluePairClass_surjective (hodd : Odd d) : Function.Surjective (gluePairClass hodd) := by
  intro a
  rcases a with i | ⟨⟨i,j⟩,hn⟩
  · exact ⟨(.inl i,0),rfl⟩
  · revert hn
    refine Fin.cases ?_ (fun j' => ?_) j
    · refine Fin.cases ?_ (fun i' => ?_) i
      · exact fun hn => (hn rfl).elim
      · exact fun _ => ⟨(.inl i',1),rfl⟩
    · obtain ⟨⟨r,b⟩,he⟩ := (glueHalfEquiv hodd).surjective j'
      intro _
      refine ⟨(.inr (i,r),b),congrArg Sum.inr (Subtype.ext ?_)⟩
      exact Prod.ext rfl (congrArg Fin.succ he)

def gluePairIndex (hodd : Odd d) (t : GluePairName d) (b : Fin 2) : GlueIndex d :=
  (t.1, gluePairClass hodd (t.2,b))

theorem gluePairIndex_bijective (hodd : Odd d) :
    Function.Bijective (fun t : GluePairName d × Fin 2 => gluePairIndex hodd t.1 t.2) := by
  constructor
  · rintro ⟨⟨j,a⟩,b⟩ ⟨⟨k,c⟩,z⟩ h
    obtain rfl : j = k := congrArg Prod.fst h
    have he := gluePairClass_injective hodd (congrArg Prod.snd h)
    rcases Prod.ext_iff.mp he with ⟨rfl,rfl⟩
    rfl
  · rintro ⟨j,a⟩
    obtain ⟨⟨t,b⟩,he⟩ := gluePairClass_surjective hodd a
    exact ⟨((j,t),b),Prod.ext rfl he⟩

def gluePair (hodd : Odd d) (t : GluePairName d) : Set (Edge (Fin n)) :=
  Set.range (fun b => glueEdge emb (gluePairIndex hodd t b))

def gluePairFamily (hodd : Odd d) : Set (Set (Edge (Fin n))) :=
  Set.range (gluePair emb hodd)

theorem glue_pair_cross (hodd : Odd d) (j : GlueJ d) (i : GlueT d) :
    gluePair emb hodd (j,.inl i) =
      {glueEdge emb (j,.inl i),glueEdge emb (j,.inr (glueCrossGadget i))} := by
  ext x
  constructor
  · rintro ⟨b,rfl⟩
    fin_cases b <;> simp [gluePairIndex,gluePairClass]
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨0,rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨1,rfl⟩

theorem glue_pair_disjoint (hodd : Odd d) {t u : GluePairName d} (hne : t ≠ u) :
    Disjoint (gluePair emb hodd t) (gluePair emb hodd u) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨a,rfl⟩ ⟨b,hb⟩
  have he : (u,b) = (t,a) := (gluePairIndex_bijective hodd).1 (glueEdge_injective emb hb)
  exact hne (congrArg Prod.fst he).symm

theorem glue_pair_two (hodd : Odd d) (t : GluePairName d) :
    (gluePair emb hodd t).ncard = 2 := by
  rw [gluePair, Set.ncard_range_of_injective]
  · simp
  · intro a b h
    have he : (t,a) = (t,b) := (gluePairIndex_bijective hodd).1 (glueEdge_injective emb h)
    exact congrArg Prod.snd he

theorem glue_pairs_cover (hodd : Odd d) :
    ⋃₀ gluePairFamily emb hodd = glueGround emb := by
  ext e
  constructor
  · rintro ⟨_,⟨t,rfl⟩,b,rfl⟩
    exact ⟨_,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨⟨t,b⟩,rfl⟩ := (gluePairIndex_bijective hodd).2 a
    exact ⟨_,⟨t,rfl⟩,b,rfl⟩

def glueSpan (E : Set (Edge (Fin n))) : Submodule F W :=
  Submodule.span F (genericRow (D := Fin d) '' E)

def glueSynthesis (a : GlueIndex d → F) : W :=
  ∑ e, a e • glueRows emb e

theorem glue_span_iff (P : GlueIndex d → Prop) [DecidablePred P] (r : W) :
    r ∈ glueSpan (glueSubset emb P) ↔
      ∃ a, glueSynthesis emb a = r ∧ ∀ e, ¬ P e → a e = 0 := by
  let f := Fintype.linearCombination F (fun e : {e // P e} => glueRows emb e.1)
  have hr : LinearMap.range f = glueSpan (glueSubset emb P) := by
    rw [glueSpan,Fintype.range_linearCombination]
    congr 1
    ext z
    exact ⟨fun ⟨⟨e,he⟩,hz⟩ => ⟨glueEdge emb e,⟨e,he,rfl⟩,hz⟩,
      fun ⟨_,⟨e,he,rfl⟩,hz⟩ => ⟨⟨e,he⟩,hz⟩⟩
  rw [← hr]
  constructor
  · rintro ⟨b,hb⟩
    have hz (e : GlueIndex d) (he : ¬ P e) := zeroExtend_off P b he
    refine ⟨zeroExtend P b, ?_,hz⟩
    rw [glueSynthesis, ← supported_sum (glueRows emb) P _ hz]
    change Fintype.linearCombination F _ b = r at hb
    rw [Fintype.linearCombination_apply] at hb
    simpa only [zeroExtend_on] using hb
  · rintro ⟨a,ha,hP⟩
    exact ⟨fun e => a e.1, (supported_sum (glueRows emb) P a hP).trans ha⟩

def glueNormalized (hd : 5 ≤ d) (a : GlueIndex d → F) (e : GlueIndex d) : F :=
  a e / glueWeight emb hd e

theorem glue_normalized_difference (hd : 5 ≤ d) (a b : GlueIndex d → F)
    (h : glueSynthesis emb a = glueSynthesis emb b)
    (e f : GlueIndex d) (hef : e.1 = f.1) :
    glueNormalized emb hd a e - glueNormalized emb hd a f =
      glueNormalized emb hd b e - glueNormalized emb hd b f := by
  have hrs : a-b ∈ relationSpace (glueRows emb) := by
    change (∑ t, (a t-b t) • glueRows emb t) = 0
    simp only [sub_smul,Finset.sum_sub_distrib]
    change glueSynthesis emb a - glueSynthesis emb b = 0
    exact sub_eq_zero.mpr h
  obtain ⟨c,hc⟩ := (glueParameterEquiv emb hd).surjective ⟨a-b,hrs⟩
  have he (i : GlueIndex d) : glueNormalized emb hd a i - glueNormalized emb hd b i = c.1 i.1 := by
    have hi := glue_factor emb hd c i
    rw [hc] at hi
    change a i - b i = glueWeight emb hd i * c.1 i.1 at hi
    rw [glueNormalized,glueNormalized, ← sub_div, hi, mul_comm,
      mul_div_cancel_right₀ _ (glueWeight_ne emb hd i)]
  have ha := he e
  have hb := he f
  rw [hef] at ha
  linear_combination ha - hb

theorem glue_normalized_iff_delete (hd : 5 ≤ d) (hodd : Odd d)
    (a : GlueIndex d → F) (t : GluePairName d) :
    glueSynthesis emb a ∈ glueSpan (glueGround emb \ gluePair emb hodd t) ↔
      glueNormalized emb hd a (gluePairIndex hodd t 0) =
      glueNormalized emb hd a (gluePairIndex hodd t 1) := by
  classical
  let e := gluePairIndex hodd t 0
  let f := gluePairIndex hodd t 1
  let P := fun i : GlueIndex d => i ≠ e ∧ i ≠ f
  have hP : glueSubset emb P = glueGround emb \ gluePair emb hodd t := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      refine ⟨⟨i,rfl⟩,?_⟩
      rintro ⟨b,hb⟩
      have eq := glueEdge_injective emb hb
      fin_cases b
      · exact hi.1 eq.symm
      · exact hi.2 eq.symm
    · rintro ⟨⟨i,rfl⟩,hi⟩
      exact ⟨i,⟨fun h => hi ⟨0,congrArg (glueEdge emb) h.symm⟩,
        fun h => hi ⟨1,congrArg (glueEdge emb) h.symm⟩⟩,rfl⟩
  rw [← hP,glue_span_iff]
  constructor
  · rintro ⟨b,hb,hz⟩
    have he : b e = 0 := hz e (fun h => h.1 rfl)
    have hf : b f = 0 := hz f (fun h => h.2 rfl)
    apply sub_eq_zero.mp
    rw [glue_normalized_difference emb hd a b hb.symm e f rfl]
    simp [glueNormalized,he,hf]
  · intro heq
    obtain ⟨c,hc⟩ := glue_coordinate_surjective emb t.1 (glueNormalized emb hd a e)
    let m := glueParameterEquiv emb hd c
    have hz : glueSynthesis emb m.1 = 0 := m.2
    refine ⟨a-m.1, ?_,?_⟩
    · change (∑ i, (a i - m.1 i) • glueRows emb i) = glueSynthesis emb a
      simp only [sub_smul, Finset.sum_sub_distrib]
      change glueSynthesis emb a - glueSynthesis emb m.1 = glueSynthesis emb a
      rw [hz,sub_zero]
    · intro i hi
      have h : i = e ∨ i = f := by
        by_cases he : i = e
        · exact Or.inl he
        · exact Or.inr (by_contra fun hf => hi ⟨he,hf⟩)
      have hh (k : GlueIndex d) (hkt : k.1 = t.1)
          (ha : glueNormalized emb hd a k = glueNormalized emb hd a e) :
          (a-m.1) k = 0 := by
        change a k - m.1 k = 0
        rw [glue_factor, hkt, show c.1 t.1 = _ from hc, ← ha, glueNormalized,
          mul_comm, div_mul_cancel₀ _ (glueWeight_ne emb hd k), sub_self]
      rcases h with rfl | rfl
      · exact hh _ rfl rfl
      · exact hh _ rfl heq.symm

#print axioms gluePairIndex_bijective
#print axioms glue_pair_cross
#print axioms glue_pair_disjoint
#print axioms glue_pair_two
#print axioms glue_pairs_cover
#print axioms glue_span_iff
#print axioms glue_normalized_difference
#print axioms glue_normalized_iff_delete

end
end Rigidity369952
```

## GlueLocalSeparation.lean

```lean
import GluePairs

open scoped BigOperators

namespace Rigidity369952

noncomputable section

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)
local notation "W" => (Fin n × Fin d → F)
local notation "p" => (genericPosition (V := Fin n) (D := Fin d))

def ambientEdge {a b : Fin n} (h : a ≠ b) : Edge (Fin n) :=
  ⟨s(a,b), fun hdiag => h (Sym2.mk_isDiag_iff.mp hdiag)⟩

theorem ambientEdge_swap {a b : Fin n} (h : a ≠ b) :
    ambientEdge h = ambientEdge h.symm := by apply Subtype.ext; exact Sym2.eq_swap

theorem generic_position_ne {a b : Fin n} (h : a ≠ b) (k : Fin d) :
    p (a,k) ≠ p (b,k) := by
  intro he
  exact h (congrArg Prod.fst (MvPolynomial.X_injective
    (IsFractionRing.injective (Poly (Fin n) (Fin d)) F he)))

theorem generic_edge_at_left {a b : Fin n} (h : a ≠ b) (k : Fin d) :
    genericRow (D := Fin d) (ambientEdge h) (a,k) = p (a,k) - p (b,k) := by
  simp [genericRow,ambientEdge,edgeRow_pair,orderedRow,h]

theorem generic_edge_at_right {a b : Fin n} (h : a ≠ b) (k : Fin d) :
    genericRow (D := Fin d) (ambientEdge h) (b,k) = p (b,k) - p (a,k) := by
  rw [ambientEdge_swap h]
  exact generic_edge_at_left h.symm k

theorem generic_edge_zero {a b w : Fin n} (h : a ≠ b) (k : Fin d)
    (ha : w ≠ a) (hb : w ≠ b) :
    genericRow (D := Fin d) (ambientEdge h) (w,k) = 0 := by
  simp [genericRow,ambientEdge,edgeRow_pair,orderedRow,ha,hb]

theorem glue_synthesis_mem (c : GlueIndex d → F) :
    glueSynthesis emb c ∈ glueSpan (d := d) (glueGround emb) :=
  Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨glueEdge emb e,⟨e,rfl⟩,rfl⟩)

theorem glue_synthesis_of_mem {r : W} (h : r ∈ glueSpan (d := d) (glueGround emb)) :
    ∃ c, glueSynthesis emb c = r := by
  have hs : glueSubset emb (fun _ => True) = glueGround emb := by
    ext x
    exact ⟨fun ⟨e,_,he⟩ => ⟨e,he⟩,fun ⟨e,he⟩ => ⟨e,trivial,he⟩⟩
  rw [← hs, glue_span_iff] at h
  obtain ⟨c,hc,_⟩ := h
  exact ⟨c,hc⟩

theorem glue_deleted_span_le (hodd : Odd d) (t : GluePairName d) :
    glueSpan (d := d) (glueGround emb \ gluePair emb hodd t) ≤ glueSpan (d := d) (glueGround emb) :=
  Submodule.span_mono (Set.image_mono Set.sdiff_subset)

theorem glue_synthesis_zero_unused (c : GlueIndex d → F) {w : Fin n}
    (hw : w ∉ Set.range emb) (k : Fin d) : glueSynthesis emb c (w,k) = 0 := by
  simp only [glueSynthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro e _
  rw [glueRows,glueEdge_eq_bipEdge]
  change c e * crossRows (D := Fin d) emb (glueColumn e.1 e.2) (w,k) = 0
  rw [crossRows_zero_of_other_vertex emb (glueColumn e.1 e.2) w k
    (fun he => hw ⟨_,he.symm⟩) (fun he => hw ⟨_,he.symm⟩), mul_zero]

theorem glue_unused_not_mem (hd : 5 ≤ d) {a b : Fin n}
    (hab : a ≠ b) (ha : a ∉ Set.range emb) :
    genericRow (D := Fin d) (ambientEdge hab) ∉ glueSpan (d := d) (glueGround emb) := by
  intro h
  obtain ⟨c,hc⟩ := glue_synthesis_of_mem emb h
  let k : Fin d := ⟨0,by omega⟩
  have he := congrFun hc (a,k)
  rw [glue_synthesis_zero_unused emb c ha, generic_edge_at_left] at he
  exact generic_position_ne hab k (sub_eq_zero.mp he.symm)

theorem glue_gadget_force_mem (c : GlueIndex d → F) (j : GlueJ d) :
    glueGadgetForce emb c j ∈ glueSpan (d := d) (completeBipartite (glueLocal emb j)) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨bipEdge (glueLocal emb j) a.1,⟨a.1,rfl⟩,rfl⟩)

theorem glue_gadget_force_mem_ground (c : GlueIndex d → F) (j : GlueJ d) :
    glueGadgetForce emb c j ∈ glueSpan (d := d) (glueGround emb) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨glueEdge emb (j,.inr a),⟨_,rfl⟩,rfl⟩)

theorem glue_recompress_outside (hd : 5 ≤ d) (c : GlueIndex d → F) (j : GlueJ d)
    {a b : GlueS d ⊕ GlueS d} (hab : a ≠ b)
    (hc : glueSynthesis emb c = genericRow (D := Fin d)
      (ambientEdge (fun h => hab ((glueLocal emb j).injective h)))) :
    ∃ z : F, glueSynthesis emb c - glueGadgetForce emb c j =
      z • crossRows (D := Fin d) (glueBase emb) (0,j) := by
  let k : Fin d := ⟨0,by omega⟩
  apply generic_two_vertex_seam (glueGround emb) (leftVertex (glueBase emb) 0)
    (rightVertex (glueBase emb) j) (cross_ne (glueBase emb) 0 j) k
  · exact (glueSpan (d := d) (glueGround emb)).sub_mem
      (glue_synthesis_mem emb c) (glue_gadget_force_mem_ground emb c j)
  · intro w i hwa hwb
    change glueSynthesis emb c (w,i) - glueGadgetForce emb c j (w,i) = 0
    by_cases hi : IsGlueInternal emb j w
    · exact sub_eq_zero.mpr (glue_force_at_internal emb c hi i)
    · have hloc (v : GlueS d ⊕ GlueS d) : w ≠ glueLocal emb j v := by
        intro he
        rcases glue_local_vertex_cases emb j v with h | h | h
        · exact hwa (he.trans h)
        · exact hwb (he.trans h)
        · exact hi (he.symm ▸ h)
      rw [hc, generic_edge_zero _ _ (hloc a) (hloc b),
        glue_gadget_force_zero emb c j w i hwa hwb hi,sub_zero]

theorem glue_same_side_not_mem (hd : 5 ≤ d) (j : GlueJ d)
    {a b : GlueS d ⊕ GlueS d} (hab : a ≠ b)
    (hside : (∃ x y, a = Sum.inl x ∧ b = Sum.inl y) ∨
      (∃ x y, a = Sum.inr x ∧ b = Sum.inr y)) :
    genericRow (D := Fin d) (ambientEdge (fun h => hab ((glueLocal emb j).injective h))) ∉
      glueSpan (d := d) (glueGround emb) := by
  intro h
  obtain ⟨c,hc⟩ := glue_synthesis_of_mem emb h
  obtain ⟨z,hz⟩ := glue_recompress_outside emb hd c j hab hc
  let E := glueSpan (d := d) (completeBipartite (glueLocal emb j))
  have hf : glueGadgetForce emb c j ∈ E := glue_gadget_force_mem emb c j
  have hs : crossRows (D := Fin d) (glueBase emb) (0,j) ∈ E := by
    change genericRow (bipEdge (glueBase emb) (0,j)) ∈ E
    rw [← glue_seam_edge]
    exact Submodule.subset_span ⟨_,⟨(0,0),rfl⟩,rfl⟩
  have hr : glueSynthesis emb c ∈ E := by
    rw [← sub_add_cancel (glueSynthesis emb c) (glueGadgetForce emb c j), hz]
    exact E.add_mem (E.smul_mem _ hs) hf
  rw [hc] at hr
  exact Kss_same_side_generic_separation d hd (glueLocal emb j) a b hab hside hr

#print axioms ambientEdge_swap
#print axioms generic_position_ne
#print axioms glue_synthesis_of_mem
#print axioms glue_unused_not_mem
#print axioms glue_recompress_outside
#print axioms glue_same_side_not_mem

end
end Rigidity369952
```

## GlueBaseSeparation.lean

```lean
import GlueLocalSeparation

open scoped BigOperators

namespace Rigidity369952

noncomputable section

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)
local notation "p" => (genericPosition (V := Fin n) (D := Fin d))

theorem base_force_left (b : GlueS d × GlueJ d → F) (i : GlueS d) (k : Fin d) :
    (∑ e, b e • crossRows (D := Fin d) (glueBase emb) e) (leftVertex (glueBase emb) i,k) =
      ∑ j, b (i,j) * (p (leftVertex (glueBase emb) i,k) - p (rightVertex (glueBase emb) j,k)) := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    crossRows, genericRow, bipEdge, edgeRow_pair, orderedRow,
    leftVertex, rightVertex, Function.Embedding.apply_eq_iff_eq, Sum.inl.injEq,
    Sum.inl_ne_inr, ite_false, add_zero, mul_ite, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

theorem base_force_right (b : GlueS d × GlueJ d → F) (j : GlueJ d) (k : Fin d) :
    (∑ e, b e • crossRows (D := Fin d) (glueBase emb) e) (rightVertex (glueBase emb) j,k) =
      ∑ i, b (i,j) * (p (rightVertex (glueBase emb) j,k) - p (leftVertex (glueBase emb) i,k)) := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    crossRows, genericRow, bipEdge, edgeRow_pair, orderedRow,
    leftVertex, rightVertex, Function.Embedding.apply_eq_iff_eq, Sum.inr.injEq,
    Sum.inr_ne_inl, ite_false, zero_add, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

theorem glue_base_recompression (hd : 5 ≤ d) (hodd : Odd d)
    {a b : GlueS d ⊕ GlueJ d} (hab : a ≠ b) (c : GlueIndex d → F)
    (hc : glueSynthesis emb c = genericRow (D := Fin d)
      (ambientEdge (fun h => hab ((glueBase emb).injective h))))
    (hpair : ∀ t, glueSynthesis emb c ∈ glueSpan (glueGround emb \ gluePair emb hodd t)) :
    ∃ t : GlueJ d → F, glueSynthesis emb c =
      ∑ e : GlueS d × GlueJ d,
        (glueLambda emb hd e.1 * t e.2) • crossRows (D := Fin d) (glueBase emb) e := by
  have hrec (j : GlueJ d) := glue_gadget_recompress emb hd c j (by
    intro w hw k
    change glueSynthesis emb c (w,k) = 0
    rw [hc]
    exact generic_edge_zero _ k (glue_internal_not_base emb hw a) (glue_internal_not_base emb hw b))
  choose z hz using hrec
  let t : GlueJ d → F := fun j => z j / glueLambda emb hd 0
  have ht (j : GlueJ d) : glueLambda emb hd 0 * t j = z j := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ (glueLambda_ne emb hd 0)
  have hbase (j : GlueJ d) (i : GlueT d) : c (j,.inl i) = glueLambda emb hd i.succ * t j := by
    have h := (glue_normalized_iff_delete emb hd hodd c (j,.inl i)).mp (hpair (j,.inl i))
    change c (j,.inl i) / glueLambda emb hd i.succ =
      c (j,.inr (glueCrossGadget i)) /
        (glueLambda emb hd 0 * (glueSeams emb hd).weights j (glueCrossGadget i)) at h
    rw [glue_gadget_factor (glueSeams emb hd) c j (z j) (hz j), ← ht j] at h
    let l₀ := glueLambda emb hd 0
    let β := (glueSeams emb hd).weights j (glueCrossGadget i)
    have he : (l₀ * t j) * β / (l₀ * β) = t j := by
      rw [mul_right_comm, mul_comm (l₀ * β)]
      exact mul_div_cancel_right₀ _ (mul_ne_zero (glueLambda_ne emb hd 0)
        ((glueSeams emb hd).nonzero j (glueCrossGadget i)))
    exact ((div_eq_iff (glueLambda_ne emb hd i.succ)).mp (h.trans he)).trans (mul_comm _ _)
  refine ⟨t,?_⟩
  have hs : glueAssemble c z = fun e => glueLambda emb hd e.1 * t e.2 := by
    funext e
    obtain ⟨i,j⟩ := e
    refine Fin.cases ?_ (fun i => ?_) i
    · exact (ht j).symm
    · exact hbase j i
  change glueSynthesis emb c = ∑ e, (fun e : GlueS d × GlueJ d => glueLambda emb hd e.1 * t e.2) e • _
  rw [← hs, glue_assemble_sum, glueSynthesis, glue_sum]
  simp only [hz]

private theorem two_other_base_left (hd : 5 ≤ d) (i j : GlueS d) :
    ∃ u v : GlueS d, u ≠ i ∧ u ≠ j ∧ v ≠ i ∧ v ≠ j ∧ u ≠ v := by
  classical
  let S := (Finset.univ.erase i).erase j
  have h₁ : (Finset.univ.erase i).card = d+2-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,Fintype.card_fin]
  have h₂ : d ≤ S.card := by
    by_cases hj : j ∈ Finset.univ.erase i
    · dsimp only [S]
      rw [ Finset.card_erase_of_mem hj, h₁]
      omega
    · dsimp only [S]
      rw [ Finset.erase_eq_of_notMem hj, h₁]
      omega
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have h₃ := Finset.card_erase_of_mem hu
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < (S.erase u).card by omega)
  have hw := Finset.mem_erase.mp hv
  have hu' := Finset.mem_erase.mp hu
  have hv' := Finset.mem_erase.mp hw.2
  exact ⟨u,v,(Finset.mem_erase.mp hu'.2).1,hu'.1,
    (Finset.mem_erase.mp hv'.2).1,hv'.1,hw.1.symm⟩

theorem glue_base_edge_separation (hd : 5 ≤ d) (hodd : Odd d)
    (a b : GlueS d ⊕ GlueJ d) (hab : a ≠ b) :
    ∃ t : GluePairName d,
      genericRow (D := Fin d) (ambientEdge (fun h => hab ((glueBase emb).injective h))) ∉
        glueSpan (glueGround emb \ gluePair emb hodd t) := by
  classical
  let E := ambientEdge (fun h => hab ((glueBase emb).injective h))
  let R := genericRow (D := Fin d) E
  by_contra! hs
  change ∀ t : GluePairName d, R ∈ glueSpan (glueGround emb \ gluePair emb hodd t) at hs
  obtain ⟨c,hc⟩ := glue_synthesis_of_mem emb (glue_deleted_span_le emb hodd (0,.inl 0) (hs (0,.inl 0)))
  obtain ⟨t,ht⟩ := glue_base_recompression emb hd hodd hab c hc (by simpa only [hc] using hs)
  let l := glueLambda emb hd
  have hl (k : Option (Fin d)) := (mem_relationSpace _ _).mp (glueLambda_rel emb hd) k
  have hl0 : ∑ i, l i = 0 := by
    have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Option (Fin d)))) rfl (fun k _ => hl k)
    rw [Finset.sum_comm] at h
    simp only [← Finset.mul_sum, affineRow, bary_sum, mul_one, Finset.sum_const_zero] at h
    exact h
  have hlp (k : Fin d) : ∑ i, l i * p (leftVertex (glueBase emb) i,k) = 0 := hl (some k)
  have hy (j : GlueJ d) (k : Fin d) : R (rightVertex (glueBase emb) j,k) = 0 := by
    rw [← hc,ht,base_force_right]
    change (∑ i, (l i * t j) * (p (rightVertex (glueBase emb) j,k) -
      p (leftVertex (glueBase emb) i,k))) = 0
    have he (i : GlueS d) : (l i * t j) * (p (rightVertex (glueBase emb) j,k) -
        p (leftVertex (glueBase emb) i,k)) =
      t j * (l i * p (rightVertex (glueBase emb) j,k) - l i * p (leftVertex (glueBase emb) i,k)) := by ring
    simp only [he, ← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hl0, hlp, zero_mul, sub_zero, mul_zero]
  let k₀ : Fin d := ⟨0,by omega⟩
  have hab' : glueBase emb a ≠ glueBase emb b := fun h => hab ((glueBase emb).injective h)
  have hna (j : GlueJ d) : a ≠ .inr j := by
    intro h
    have he := hy j k₀
    have hh : rightVertex (glueBase emb) j = glueBase emb a := congrArg (glueBase emb) h.symm
    rw [hh] at he
    exact generic_position_ne hab' k₀ (sub_eq_zero.mp ((generic_edge_at_left hab' k₀).symm.trans he))
  have hnb (j : GlueJ d) : b ≠ .inr j := by
    intro h
    have he := hy j k₀
    have hh : rightVertex (glueBase emb) j = glueBase emb b := congrArg (glueBase emb) h.symm
    rw [hh] at he
    exact generic_position_ne hab'.symm k₀ (sub_eq_zero.mp ((generic_edge_at_right hab' k₀).symm.trans he))
  rcases a with i | i
  · rcases b with j | j
    · let A : F := ∑ j, t j
      let B (k : Fin d) : F := ∑ j, t j * p (rightVertex (glueBase emb) j,k)
      have hx (u : GlueS d) (k : Fin d) :
          R (leftVertex (glueBase emb) u,k) = l u * (A * p (leftVertex (glueBase emb) u,k) - B k) := by
        rw [← hc,ht,base_force_left]
        simp only [mul_assoc, ← Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul]
      obtain ⟨u,v,hui,huj,hvi,hvj,huv⟩ := two_other_base_left hd i j
      have hleft_ne {x y : GlueS d} (h : x ≠ y) :
          leftVertex (glueBase emb) x ≠ leftVertex (glueBase emb) y :=
        fun he => h (Sum.inl.inj ((glueBase emb).injective he))
      have hz (k : Fin d) : A * p (leftVertex (glueBase emb) u,k) = B k := by
        have h := hx u k
        rw [show R (leftVertex (glueBase emb) u,k) = 0 from
          generic_edge_zero hab' k (hleft_ne hui) (hleft_ne huj)] at h
        exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left (glueLambda_ne emb hd u))
      have hv : A * p (leftVertex (glueBase emb) v,k₀) = B k₀ := by
        have h := hx v k₀
        rw [show R (leftVertex (glueBase emb) v,k₀) = 0 from
          generic_edge_zero hab' k₀ (hleft_ne hvi) (hleft_ne hvj)] at h
        exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left (glueLambda_ne emb hd v))
      have hA : A = 0 := by
        have h : A * (p (leftVertex (glueBase emb) u,k₀) -
            p (leftVertex (glueBase emb) v,k₀)) = 0 := by rw [mul_sub,hz,hv,sub_self]
        exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (generic_position_ne (hleft_ne huv) k₀))
      have hi := hx i k₀
      have hb0 : B k₀ = 0 := (hz k₀).symm.trans (by rw [hA,zero_mul])
      rw [hA,hb0,zero_mul,sub_zero,mul_zero] at hi
      exact generic_position_ne hab' k₀ (sub_eq_zero.mp ((generic_edge_at_left hab' k₀).symm.trans hi))
    · exact hnb j rfl
  · exact hna i rfl

#print axioms glue_base_recompression
#print axioms glue_base_edge_separation

end
end Rigidity369952
```

## GlueGram.lean

```lean
import GlueLocalSeparation

open scoped BigOperators

namespace Rigidity369952

noncomputable section

section Algebra

variable {D K S : Type*} [Fintype D] [CommRing K] [CommRing S]

def glueProject (w a : D → K) : D → K :=
  (w ⬝ᵥ w) • a - (a ⬝ᵥ w) • w

def glueSkew (A B x : D → K) : D → K :=
  (B ⬝ᵥ x) • A - (A ⬝ᵥ x) • B

def glueGram (w a b : D → K) : K :=
  let A := glueProject w a
  let B := glueProject w b
  (A ⬝ᵥ a) * (B ⬝ᵥ b) - (B ⬝ᵥ a) * (A ⬝ᵥ b)

theorem glueProject_orthogonal (w a : D → K) : glueProject w a ⬝ᵥ w = 0 := by
  rw [glueProject, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]

theorem glueSkew_sub (A B x y : D → K) :
    glueSkew A B (x-y) = glueSkew A B x - glueSkew A B y := by
  simp only [glueSkew,dotProduct_sub,sub_smul]
  abel

theorem glueSkew_zero (A B : D → K) : glueSkew A B 0 = 0 := by simp [glueSkew]

theorem glueSkew_diagonal (A B x : D → K) : x ⬝ᵥ glueSkew A B x = 0 := by
  rw [glueSkew,dotProduct_sub,dotProduct_smul,dotProduct_smul]
  rw [dotProduct_comm x A, dotProduct_comm x B]
  simp only [smul_eq_mul]
  ring

theorem glueGram_eq_motion (w a b : D → K) :
    (a-b) ⬝ᵥ glueSkew (glueProject w a) (glueProject w b) a = glueGram w a b := by
  unfold glueSkew glueGram
  rw [sub_dotProduct]
  simp only [dotProduct_sub,dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm a (glueProject w a), dotProduct_comm a (glueProject w b),
    dotProduct_comm b (glueProject w a), dotProduct_comm b (glueProject w b)]
  ring

theorem glue_gram_projected (w a b : D → K) :
    let A := glueProject w a
    let B := glueProject w b
    (A ⬝ᵥ A) * (B ⬝ᵥ B) - (A ⬝ᵥ B) * (B ⬝ᵥ A) =
      (w ⬝ᵥ w)^2 * glueGram w a b := by
  have h (x y : D → K) : glueProject w x ⬝ᵥ glueProject w y =
      (w ⬝ᵥ w) * (glueProject w x ⬝ᵥ y) := by
    conv_lhs => arg 2; unfold glueProject
    simp only [dotProduct_sub,dotProduct_smul,smul_eq_mul,glueProject_orthogonal,mul_zero,sub_zero]
  dsimp only
  rw [h a a,h b b,h a b,h b a]
  unfold glueGram
  ring

theorem glue_map_dot (f : K →+* S) (a b : D → K) :
    f (a ⬝ᵥ b) = (f ∘ a) ⬝ᵥ (f ∘ b) := by simp [dotProduct,map_sum,map_mul,Function.comp_apply]

theorem glue_map_project (f : K →+* S) (w a : D → K) :
    f ∘ glueProject w a = glueProject (f ∘ w) (f ∘ a) := by
  funext i
  simp only [Function.comp_apply,glueProject,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,map_sub,
    map_mul,glue_map_dot]

theorem glue_map_gram (f : K →+* S) (w a b : D → K) :
    f (glueGram w a b) = glueGram (f ∘ w) (f ∘ a) (f ∘ b) := by
  simp only [glueGram,map_sub,map_mul,glue_map_dot,glue_map_project]

end Algebra

variable {d n : ℕ}
local notation "F" => GenericField (Fin n) (Fin d)
local notation "p" => (genericPosition (V := Fin n) (D := Fin d))

theorem glue_generic_gram_nonzero (hd : 5 ≤ d)
    {x y a b : Fin n} (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b)
    (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b) :
    glueGram (fun i => p (y,i) - p (x,i)) (fun i => p (a,i) - p (x,i))
      (fun i => p (b,i) - p (x,i)) ≠ 0 := by
  let i₁ : Fin d := ⟨0,by omega⟩
  let i₂ : Fin d := ⟨1,by omega⟩
  let i₃ : Fin d := ⟨2,by omega⟩
  have h12 : i₁ ≠ i₂ := by intro h; have hh := congrArg Fin.val h; change 0 = 1 at hh; omega
  have h13 : i₁ ≠ i₃ := by intro h; have hh := congrArg Fin.val h; change 0 = 2 at hh; omega
  have h23 : i₂ ≠ i₃ := by intro h; have hh := congrArg Fin.val h; change 1 = 2 at hh; omega
  let witness (v : Fin n) : Fin d → ℚ :=
    if v = y then Pi.single i₁ 1 else if v = a then Pi.single i₂ 1 else
      if v = b then Pi.single i₃ 1 else 0
  let f : Poly (Fin n) (Fin d) →+* ℚ :=
    (MvPolynomial.aeval (fun v : Fin n × Fin d => witness v.1 v.2)).toRingHom
  let diff (v : Fin n) (i : Fin d) : Poly (Fin n) (Fin d) :=
    MvPolynomial.X (v,i) - MvPolynomial.X (x,i)
  have he (v : Fin n) : f ∘ diff v = witness v := by
    funext i
    simp [f,diff,witness,hxy,hxa,hxb]
  have hy : witness y = Pi.single i₁ 1 := by simp [witness]
  have ha : witness a = Pi.single i₂ 1 := by simp [witness,hya.symm]
  have hb : witness b = Pi.single i₃ 1 := by simp [witness,hyb.symm,hab.symm]
  have hn : f (glueGram (diff y) (diff a) (diff b)) = 1 := by
    rw [glue_map_gram,he,he,he,hy,ha,hb]
    simp [glueGram,glueProject,h12,h13,h23,h23.symm]
  have hpoly : glueGram (diff y) (diff a) (diff b) ≠ 0 := by
    intro h
    rw [h,map_zero] at hn
    exact zero_ne_one hn
  let g := algebraMap (Poly (Fin n) (Fin d)) F
  have hg (v : Fin n) : g ∘ diff v = fun i => p (v,i) - p (x,i) := by
    funext i
    exact map_sub _ _ _
  have hh := (IsFractionRing.injective (Poly (Fin n) (Fin d)) F).ne hpoly
  change g (glueGram (diff y) (diff a) (diff b)) ≠ g 0 at hh
  rwa [glue_map_gram,hg,hg,hg,map_zero] at hh

#print axioms glue_map_gram
#print axioms glue_gram_projected
#print axioms glue_generic_gram_nonzero

end
end Rigidity369952
```

## GlueMotion.lean

```lean
import GlueGram

open scoped BigOperators

namespace Rigidity369952

noncomputable section

open scoped Classical

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)
local notation "W" => (Fin n × Fin d → F)
local notation "p" => (genericPosition (V := Fin n) (D := Fin d))

theorem glue_internal_mem_local {j : GlueJ d} {w : Fin n} (hw : IsGlueInternal emb j w) :
    w ∈ Set.range (glueLocal emb j) := by
  rcases hw with ⟨u,hu,rfl⟩
  rcases u with (i | ⟨k,i⟩) | (i | ⟨k,i⟩)
  · exact False.elim hu
  · change k = j at hu
    subst k
    exact ⟨.inl i.succ,rfl⟩
  · exact False.elim hu
  · change k = j at hu
    subst k
    exact ⟨.inr i.succ,rfl⟩

def glueOffset (x v : Fin n) : Fin d → F := fun k => p (v,k) - p (x,k)

theorem glueOffset_sub (x u v : Fin n) :
    glueOffset (d := d) x u - glueOffset x v = fun k => p (u,k) - p (v,k) := by
  funext k
  simp only [glueOffset,Pi.sub_apply]
  ring

def glueMotion (j : GlueJ d) (A B : Fin d → F) (v : Fin n) : Fin d → F :=
  if IsGlueInternal emb j v then glueSkew A B (glueOffset (leftVertex (glueBase emb) 0) v) else 0

theorem glueMotion_on_local (j : GlueJ d) (A B : Fin d → F)
    (hA : A ⬝ᵥ glueOffset (leftVertex (glueBase emb) 0) (rightVertex (glueBase emb) j) = 0)
    (hB : B ⬝ᵥ glueOffset (leftVertex (glueBase emb) 0) (rightVertex (glueBase emb) j) = 0)
    (v : GlueS d ⊕ GlueS d) :
    glueMotion emb j A B (glueLocal emb j v) =
      glueSkew A B (glueOffset (leftVertex (glueBase emb) 0) (glueLocal emb j v)) := by
  rcases glue_local_vertex_cases emb j v with h | h | h
  · rw [h,glueMotion,ite_eq_right]
    · have hz : glueOffset (d := d) (leftVertex (glueBase emb) 0) (leftVertex (glueBase emb) 0) = 0 := by
        funext k
        exact sub_self _
      rw [hz,glueSkew_zero]
    · exact fun hi => glue_internal_not_base emb hi (.inl 0) rfl
  · rw [h,glueMotion,ite_eq_right]
    · rw [glueSkew,hA,hB,zero_smul,zero_smul,sub_zero]
    · exact fun hi => glue_internal_not_base emb hi (.inr j) rfl
  · exact ite_eq_left h

def glueWork (vel : Fin n → Fin d → F) : W →ₗ[F] F where
  toFun f := ∑ v : Fin n, (fun k => f (v,k)) ⬝ᵥ vel v
  map_add' a b := by
    simp only [Pi.add_apply, ← Pi.add_def, add_dotProduct,Finset.sum_add_distrib]
  map_smul' c f := by
    change (∑ v, (c • fun k => f (v,k)) ⬝ᵥ vel v) = c • (∑ v, (fun k => f (v,k)) ⬝ᵥ vel v)
    simp only [smul_dotProduct, ← Finset.smul_sum]

theorem glue_work_edge (vel : Fin n → Fin d → F) {u v : Fin n} (huv : u ≠ v) :
    glueWork vel (genericRow (D := Fin d) (ambientEdge huv)) =
      (fun k => p (u,k) - p (v,k)) ⬝ᵥ (vel u - vel v) := by
  classical
  change (∑ w : Fin n, (fun k => genericRow (D := Fin d) (ambientEdge huv) (w,k)) ⬝ᵥ vel w) = _
  have h (w : Fin n) : (fun k => genericRow (D := Fin d) (ambientEdge huv) (w,k)) =
      (if w = u then fun k => p (u,k) - p (v,k) else 0) +
      (if w = v then fun k => p (v,k) - p (u,k) else 0) := by
    funext k
    by_cases hu : w = u <;> by_cases hv : w = v <;>
      simp [genericRow,ambientEdge,edgeRow_pair,orderedRow,hu,hv,huv,huv.symm]
  have hi (w z : Fin n) (q : Fin d → F) :
      (if w = z then q else 0) ⬝ᵥ vel w = if w = z then q ⬝ᵥ vel w else 0 := by
    by_cases hw : w = z <;> simp [hw]
  simp only [h,add_dotProduct,Finset.sum_add_distrib,hi]
  rw [Finset.sum_ite_eq',Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _),
    dotProduct_sub]
  have he : (fun k => p (v,k) - p (u,k)) = -(fun k => p (u,k) - p (v,k)) := by
    funext k
    exact (neg_sub _ _).symm
  rw [he,neg_dotProduct,sub_eq_add_neg]

theorem glue_cross_gadget_separation (hd : 5 ≤ d) (j : GlueJ d) {a b : Fin n}
    (ha : IsGlueInternal emb j a) (hb : b ∉ Set.range (glueLocal emb j))
    (hab : a ≠ b) :
    genericRow (D := Fin d) (ambientEdge hab) ∉ glueSpan (glueGround emb) := by
  let x := leftVertex (glueBase emb) 0
  let y := rightVertex (glueBase emb) j
  let w := glueOffset (d := d) x y
  let α := glueOffset (d := d) x a
  let β := glueOffset (d := d) x b
  let A := glueProject w α
  let B := glueProject w β
  let vel := glueMotion emb j A B
  let φ := glueWork vel
  have hA : A ⬝ᵥ w = 0 := glueProject_orthogonal _ _
  have hB : B ⬝ᵥ w = 0 := glueProject_orthogonal _ _
  have hx : x ∈ Set.range (glueLocal emb j) := ⟨.inl 0,rfl⟩
  have hy : y ∈ Set.range (glueLocal emb j) := ⟨.inr 0,rfl⟩
  have hzero (v : Fin n) (h : ¬ IsGlueInternal emb j v) : vel v = 0 := ite_eq_right h
  have hbase (v : GlueS d ⊕ GlueJ d) : vel (glueBase emb v) = 0 :=
    hzero _ fun h => glue_internal_not_base emb h v rfl
  have hother (l : GlueJ d) (hl : l ≠ j) (v : GlueS d ⊕ GlueS d) :
      vel (glueLocal emb l v) = 0 := by
    rcases glue_local_vertex_cases emb l v with hv | hv | hv
    · rw [hv]; exact hbase (.inl 0)
    · rw [hv]; exact hbase (.inr l)
    · exact hzero _ fun hh => hl (glue_internal_unique emb hv hh)
  have hrow (e : GlueIndex d) : φ (glueRows emb e) = 0 := by
    rcases e with ⟨l,i | g⟩
    · change φ (genericRow (ambientEdge (cross_ne (glueBase emb) i.succ l))) = 0
      rw [show φ = glueWork vel from rfl, glue_work_edge,
        show vel (leftVertex (glueBase emb) i.succ) = 0 from hbase (.inl i.succ),
        show vel (rightVertex (glueBase emb) l) = 0 from hbase (.inr l),
        sub_zero,dotProduct_zero]
    · change φ (genericRow (ambientEdge (cross_ne (glueLocal emb l) g.1.1 g.1.2))) = 0
      rw [show φ = glueWork vel from rfl, glue_work_edge]
      by_cases h : l = j
      · subst l
        let u := leftVertex (glueLocal emb j) g.1.1
        let v := rightVertex (glueLocal emb j) g.1.2
        change (fun k => p (u,k) - p (v,k)) ⬝ᵥ (vel u - vel v) = 0
        rw [← glueOffset_sub x u v, show vel u = _ from
          glueMotion_on_local emb j A B hA hB (.inl g.1.1),
          show vel v = _ from glueMotion_on_local emb j A B hA hB (.inr g.1.2),
          ← glueSkew_sub]
        exact glueSkew_diagonal _ _ _
      · rw [show vel (leftVertex (glueLocal emb l) g.1.1) = 0 from hother l h (.inl g.1.1),
          show vel (rightVertex (glueLocal emb l) g.1.2) = 0 from hother l h (.inr g.1.2),
          sub_zero,dotProduct_zero]
  intro hr
  obtain ⟨c,hc⟩ := glue_synthesis_of_mem emb hr
  have hz : φ (glueSynthesis emb c) = 0 := by
    simp only [glueSynthesis,map_sum,map_smul,hrow,smul_zero,Finset.sum_const_zero]
  rw [hc,show φ = glueWork vel from rfl,glue_work_edge,
    show vel a = glueSkew A B α from ite_eq_left ha,
    hzero b (fun hi => hb (glue_internal_mem_local emb hi)),sub_zero,← glueOffset_sub x a b,
    glueGram_eq_motion] at hz
  exact glue_generic_gram_nonzero (x := x) (y := y) (a := a) (b := b) hd (cross_ne (glueBase emb) 0 j)
    (glue_internal_not_base emb ha (.inl 0)).symm
    (fun he => hb (he ▸ hx)) (glue_internal_not_base emb ha (.inr j)).symm
    (fun he => hb (he ▸ hy)) hab hz

#print axioms glue_internal_mem_local
#print axioms glue_work_edge
#print axioms glue_cross_gadget_separation

end
end Rigidity369952
```

## GlueAmbient.lean

```lean
import GlueBaseSeparation
import GlueMotion

open scoped BigOperators

namespace Rigidity369952

noncomputable section

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)

def glueSeamSet : Set (Edge (Fin n)) :=
  Set.range (fun j : GlueJ d => bipEdge (glueBase emb) (0,j))

theorem glue_deleted_seam (j : GlueJ d) : bipEdge (glueBase emb) (0,j) ∉ glueGround emb := by
  rintro ⟨⟨l,i | a⟩,h⟩
  · have hh : (i.succ,l) = (0,j) := bipEdge_injective (glueBase emb) h
    exact Fin.succ_ne_zero i (congrArg Prod.fst hh)
  · have hh : glueColumn l (.inr a) = ((Sum.inl 0),(Sum.inl j)) := by
      apply bipEdge_injective emb
      change glueEdge emb (l,.inr a) = bipEdge (glueBase emb) (0,j)
      exact h
    have hl : l = j := by
      have hc := congrArg (glueRightCol ∘ Prod.snd) hh
      rw [show (glueRightCol ∘ Prod.snd) (glueColumn l (.inr a)) = l from glueColumn_right l (.inr a)] at hc
      exact hc
    subst l
    have he : bipEdge (glueLocal emb j) a.1 = bipEdge (glueLocal emb j) (0,0) :=
      h.trans (glue_seam_edge emb j).symm
    exact a.2 (bipEdge_injective (glueLocal emb j) he)

theorem glue_ground_literal :
    glueGround emb =
      (completeBipartite (glueBase emb) ∪
        ⋃ j : GlueJ d, completeBipartite (glueLocal emb j)) \ glueSeamSet emb := by
  ext x
  constructor
  · rintro ⟨⟨j,i | a⟩,rfl⟩
    · exact ⟨Or.inl ⟨(i.succ,j),rfl⟩,
        fun ⟨l,hl⟩ => glue_deleted_seam emb l ⟨_,hl.symm⟩⟩
    · exact ⟨Or.inr (Set.mem_iUnion.mpr ⟨j,a.1,rfl⟩),
        fun ⟨l,hl⟩ => glue_deleted_seam emb l ⟨_,hl.symm⟩⟩
  · rintro ⟨h,hns⟩
    rcases h with ⟨⟨i,j⟩,rfl⟩ | h
    · revert hns
      refine Fin.cases ?_ (fun l => ?_) i
      · exact fun hn => (hn ⟨j,rfl⟩).elim
      · exact fun _ => ⟨(j,.inl l),rfl⟩
    · obtain ⟨j,⟨a,rfl⟩⟩ := Set.mem_iUnion.mp h
      have hne : a ≠ (0,0) := by
        intro he
        subst a
        exact hns ⟨j,(glue_seam_edge emb j).symm⟩
      exact ⟨(j,.inr ⟨a,hne⟩),rfl⟩

theorem glue_used_base_or_internal {w : Fin n} (h : w ∈ Set.range emb) :
    w ∈ Set.range (glueBase emb) ∨ ∃ j, IsGlueInternal emb j w := by
  rcases h with ⟨v,rfl⟩
  rcases v with (i | ⟨j,i⟩) | (i | ⟨j,i⟩)
  · exact Or.inl ⟨.inl i,rfl⟩
  · exact Or.inr ⟨j,Sum.inl (Sum.inr (j,i)),rfl,rfl⟩
  · exact Or.inl ⟨.inr i,rfl⟩
  · exact Or.inr ⟨j,Sum.inr (Sum.inr (j,i)),rfl,rfl⟩

theorem glue_internal_edge_separation (hd : 5 ≤ d) (j : GlueJ d) {a b : Fin n}
    (ha : IsGlueInternal emb j a) (hab : a ≠ b) (he : ambientEdge hab ∉ glueGround emb) :
    genericRow (D := Fin d) (ambientEdge hab) ∉ glueSpan (glueGround emb) := by
  by_cases hl : b ∈ Set.range (glueLocal emb j)
  · obtain ⟨u,rfl⟩ := glue_internal_mem_local emb ha
    obtain ⟨v,rfl⟩ := hl
    have huv : u ≠ v := fun h => hab (congrArg (glueLocal emb j) h)
    have hnot (k : GlueS d ⊕ GlueS d) (hk : IsGlueInternal emb j (glueLocal emb j k))
        : k ≠ .inl 0 ∧ k ≠ .inr 0 := by
      constructor
      · rintro rfl
        exact glue_internal_not_base emb hk (.inl 0) rfl
      · rintro rfl
        exact glue_internal_not_base emb hk (.inr j) rfl
    obtain ⟨hleft,hright⟩ := hnot u ha
    rcases u with i | i <;> rcases v with k | k
    · exact glue_same_side_not_mem emb hd j huv (Or.inl ⟨_,_,rfl,rfl⟩)
    · have hn : (i,k) ≠ ((0,0) : GlueS d × GlueS d) :=
        fun h => hleft (congrArg Sum.inl (congrArg Prod.fst h))
      exact False.elim (he ⟨(j,.inr ⟨(i,k),hn⟩),rfl⟩)
    · have hn : (k,i) ≠ ((0,0) : GlueS d × GlueS d) :=
        fun h => hright (congrArg Sum.inr (congrArg Prod.snd h))
      exact False.elim (he ⟨(j,.inr ⟨(k,i),hn⟩),(ambientEdge_swap hab).symm⟩)
    · exact glue_same_side_not_mem emb hd j huv (Or.inr ⟨_,_,rfl,rfl⟩)
  · exact glue_cross_gadget_separation emb hd j ha hl hab

theorem glue_ambient_separation (hd : 5 ≤ d) (hodd : Odd d)
    (e : Edge (Fin n)) (he : e ∉ glueGround emb) :
    ∃ t : GluePairName d, genericRow (D := Fin d) e ∉
      glueSpan (glueGround emb \ gluePair emb hodd t) := by
  obtain ⟨z,hz⟩ := e
  induction z using Sym2.inductionOn with
  | _ a b =>
    have hab : a ≠ b := fun h => hz (Sym2.mk_isDiag_iff.mpr h)
    change ambientEdge hab ∉ glueGround emb at he
    change ∃ t : GluePairName d, genericRow (D := Fin d) (ambientEdge hab) ∉ _
    have lift (h : genericRow (D := Fin d) (ambientEdge hab) ∉ glueSpan (glueGround emb)) :
        ∃ t : GluePairName d, genericRow (D := Fin d) (ambientEdge hab) ∉
          glueSpan (glueGround emb \ gluePair emb hodd t) :=
      ⟨(0,.inl 0),fun ht => h (glue_deleted_span_le emb hodd _ ht)⟩
    by_cases ha : a ∈ Set.range emb
    · by_cases hb : b ∈ Set.range emb
      · rcases glue_used_base_or_internal emb ha with ha | ⟨j,hj⟩
        · rcases glue_used_base_or_internal emb hb with hb | ⟨j,hj⟩
          · obtain ⟨u,rfl⟩ := ha
            obtain ⟨v,rfl⟩ := hb
            exact glue_base_edge_separation emb hd hodd u v (fun h => hab (congrArg (glueBase emb) h))
          · apply lift
            rw [ambientEdge_swap hab]
            exact glue_internal_edge_separation emb hd j hj hab.symm
              (by rwa [← ambientEdge_swap hab])
        · exact lift (glue_internal_edge_separation emb hd j hj hab he)
      · apply lift
        rw [ambientEdge_swap hab]
        exact glue_unused_not_mem emb hd hab.symm hb
    · exact lift (glue_unused_not_mem emb hd hab ha)

theorem glue_ambient_family_separation (hd : 5 ≤ d) (hodd : Odd d)
    (e : Edge (Fin n)) (he : e ∉ glueGround emb) :
    ∃ P ∈ gluePairFamily emb hodd, genericRow (D := Fin d) e ∉ glueSpan (glueGround emb \ P) := by
  obtain ⟨t,ht⟩ := glue_ambient_separation emb hd hodd e he
  exact ⟨_,⟨t,rfl⟩,ht⟩

theorem glue_ambient_fin (d n : ℕ) (hd : 5 ≤ d) (hodd : Odd d)
    (hn : 2*(d+2)^2 + 2*(d+2) - 1 ≤ n) :
    ∀ e : Edge (Fin n), e ∉ glueGround (glueEmbedding d n hn) →
      ∃ P ∈ gluePairFamily (glueEmbedding d n hn) hodd,
        genericRow (D := Fin d) e ∉
          glueSpan (glueGround (glueEmbedding d n hn) \ P) :=
  glue_ambient_family_separation (glueEmbedding d n hn) hd hodd

#print axioms glue_deleted_seam
#print axioms glue_ground_literal
#print axioms glue_internal_edge_separation
#print axioms glue_ambient_separation
#print axioms glue_ambient_family_separation
#print axioms glue_ambient_fin

end
end Rigidity369952
```

## GlueWitness.lean

```lean
import GlueAmbient

open scoped BigOperators

namespace Rigidity369952

noncomputable section

variable {d n : ℕ} (emb : GlueV d ↪ Fin n)
local notation "F" => GenericField (Fin n) (Fin d)

theorem glue_local_base_labels (j : GlueJ d) :
    Set.range (glueLocal emb j) ∩ Set.range (glueBase emb) =
      {leftVertex (glueBase emb) 0, rightVertex (glueBase emb) j} := by
  ext w
  constructor
  · rintro ⟨⟨a,rfl⟩,⟨b,hb⟩⟩
    rcases glue_local_vertex_cases emb j a with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (glue_internal_not_base emb h b hb.symm).elim
  · rintro (rfl | rfl)
    · exact ⟨⟨.inl 0,rfl⟩,⟨.inl 0,rfl⟩⟩
    · exact ⟨⟨.inr 0,rfl⟩,⟨.inr j,rfl⟩⟩

theorem glue_internal_disjoint (j k : GlueJ d) (h : j ≠ k) :
    Disjoint {w | IsGlueInternal emb j w} {w | IsGlueInternal emb k w} :=
  Set.disjoint_left.mpr fun _ hj hk => h (glue_internal_unique emb hj hk)

theorem glue_pair_family_disjoint (hodd : Odd d) :
    (gluePairFamily emb hodd).PairwiseDisjoint id := by
  rintro _ ⟨t,rfl⟩ _ ⟨u,rfl⟩ h
  exact glue_pair_disjoint emb hodd (fun he => h (congrArg (gluePair emb hodd) he))

theorem glue_pair_family_two (hodd : Odd d) {P : Set (Edge (Fin n))}
    (hP : P ∈ gluePairFamily emb hodd) : P.ncard = 2 := by
  rcases hP with ⟨t,rfl⟩
  exact glue_pair_two emb hodd t

theorem glue_pair_family_card (hodd : Odd d) :
    (gluePairFamily emb hodd).ncard = (d+3) * ((d+2)^2 + (d+2) - 2) / 2 := by
  have hMap : Function.Injective (gluePair emb hodd) := by
    intro t u he
    by_contra h
    have hd := glue_pair_disjoint emb hodd h
    rw [he] at hd
    have hm : glueEdge emb (gluePairIndex hodd u 0) ∈ gluePair emb hodd u := ⟨0,rfl⟩
    exact Set.disjoint_left.mp hd hm hm
  rw [gluePairFamily, Set.ncard_range_of_injective hMap, Nat.card_eq_fintype_card]
  have hc := Fintype.card_congr (Equiv.ofBijective _ (gluePairIndex_bijective hodd))
  rw [Fintype.card_prod, Fintype.card_fin] at hc
  have hh : Fintype.card (GlueIndex d) = (d+3) * ((d+2)^2+(d+2)-2) := by
    rw [Fintype.card_prod,Fintype.card_fin,glue_class_card]
  rw [← hh, ← hc]
  omega

theorem glue_exact_column_support (hd : 5 ≤ d) (j : GlueJ d) :
    ∃ c : relationSpace (glueRows emb), ∀ e : GlueIndex d, c.1 e = 0 ↔ e.1 = j := by
  let U := LinearMap.ker (coordinate (GlueParameters emb) j)
  have hp : 0 < Module.finrank F U := by
    change 0 < Module.finrank F (LinearMap.ker (coordinate (GlueParameters emb) j))
    rw [glue_coordinate_kernel_rank]
    decide
  obtain ⟨c,hc⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := U)).mp hp
  have hj : c.1.1 j = 0 := c.2
  refine ⟨glueParameterEquiv emb hd c.1,fun e => ?_⟩
  rw [glue_stress_zero_iff]
  constructor
  · intro he
    by_contra h
    exact hc (Subtype.ext (glue_parameter_two_zero emb c.1 h he hj))
  · rintro rfl
    exact hj

theorem glue_column_classes (hd : 5 ≤ d) (e f : GlueIndex d) :
    e.1 = f.1 ↔ ∀ c : relationSpace (glueRows emb), c.1 e = 0 ↔ c.1 f = 0 := by
  constructor
  · intro h c
    obtain ⟨b,rfl⟩ := (glueParameterEquiv emb hd).surjective c
    rw [glue_stress_zero_iff,glue_stress_zero_iff,h]
  · intro h
    obtain ⟨c,hc⟩ := glue_exact_column_support emb hd f.1
    exact (hc e).mp ((h c).mpr ((hc f).mpr rfl))

theorem glue_pair_deletion_rank (hd : 5 ≤ d) (hodd : Odd d) (t : GluePairName d) :
    genericRank (D := Fin d) (glueGround emb \ gluePair emb hodd t) =
      (d+3) * ((d+2)^2 + (d+2) - 2) - 3 := by
  let e := gluePairIndex hodd t 0
  let f := gluePairIndex hodd t 1
  let S : Finset (GlueIndex d) := {e,f}
  have hef : e ≠ f := by
    intro h
    have h' : (t,(0 : Fin 2)) = (t,(1 : Fin 2)) := (gluePairIndex_bijective hodd).1 h
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd h')
  have hs : glueEdge emb '' (↑S : Set (GlueIndex d)) = gluePair emb hodd t := by
    ext a
    constructor
    · rintro ⟨i,hi,rfl⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨0,rfl⟩
      · rcases Finset.mem_singleton.mp hi with rfl
        exact ⟨1,rfl⟩
    · rintro ⟨b,rfl⟩
      fin_cases b
      · exact ⟨e,Finset.mem_insert_self _ _,rfl⟩
      · exact ⟨f,Finset.mem_insert_of_mem (Finset.mem_singleton_self _),rfl⟩
  have hc : S.card = 2 := Finset.card_pair hef
  have hr := glue_delete_same_rank emb hd S e (Finset.mem_insert_self _ _) (by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rfl
    · rcases Finset.mem_singleton.mp hi with rfl
      rfl)
  rw [glue_delete_eq,hs,hc] at hr
  omega

#print axioms glue_local_base_labels
#print axioms glue_internal_disjoint
#print axioms glue_pair_family_disjoint
#print axioms glue_pair_family_card
#print axioms glue_exact_column_support
#print axioms glue_column_classes
#print axioms glue_pair_deletion_rank

end
end Rigidity369952
```

## GlueLiteral.lean

```lean
import GlueWitness

open scoped BigOperators

namespace Rigidity369952

noncomputable section

section Reindex
variable {I J A K : Type*} [Fintype I] [Fintype J] [Field K]

def relationSpaceReindex (e : I ≃ J) (x : J → A → K) :
    relationSpace (x ∘ e) ≃ₗ[K] relationSpace x where
  toFun a := ⟨a.1 ∘ e.symm, by
    change ∑ j, (a.1 ∘ e.symm) j • x j = 0
    have h := Fintype.sum_equiv e (fun i => a.1 i • x (e i))
      (fun j => (a.1 ∘ e.symm) j • x j) (fun i => by simp)
    exact h.symm.trans a.2⟩
  invFun b := ⟨b.1 ∘ e, by
    change ∑ i, (b.1 ∘ e) i • x (e i) = 0
    have h := Fintype.sum_equiv e (fun i => (b.1 ∘ e) i • x (e i)) (fun j => b.1 j • x j)
      (fun _ => rfl)
    exact h.trans b.2⟩
  left_inv a := Subtype.ext (funext fun i => congrArg a.1 (e.symm_apply_apply i))
  right_inv b := Subtype.ext (funext fun j => congrArg b.1 (e.apply_symm_apply j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Reindex

variable {d n : ℕ}
local notation "F" => GenericField (Fin n) (Fin d)

def literalStress (E : Set (Edge (Fin n))) : Submodule F (E → F) :=
  letI : Fintype E := Fintype.ofFinite _
  relationSpace (fun e : E => genericRow (D := Fin d) e.1)

def glueLiteralBaseEquiv (emb : GlueV d ↪ Fin n) :
    stressSpace (D := Fin d) (glueBase emb) ≃ₗ[F] literalStress (d := d) (completeBipartite (glueBase emb)) :=
  letI : Fintype (completeBipartite (glueBase emb)) := Fintype.ofFinite _
  let q : (GlueS d × GlueJ d) ≃ completeBipartite (glueBase emb) :=
    Equiv.ofInjective (bipEdge (glueBase emb)) (bipEdge_injective (glueBase emb))
  relationSpaceReindex q (fun a => genericRow (D := Fin d) a.1)

def glueLiteralGroundEquiv (emb : GlueV d ↪ Fin n) :
    relationSpace (glueRows emb) ≃ₗ[F] literalStress (d := d) (glueGround emb) :=
  letI : Fintype (glueGround emb) := Fintype.ofFinite _
  let q : GlueIndex d ≃ glueGround emb := Equiv.ofInjective (glueEdge emb) (glueEdge_injective emb)
  relationSpaceReindex q (fun a => genericRow (D := Fin d) a.1)

def glueLiteralStressEquiv (emb : GlueV d ↪ Fin n) (hd : 5 ≤ d) :
    literalStress (d := d) (completeBipartite (glueBase emb)) ≃ₗ[F] literalStress (d := d) (glueGround emb) :=
  (glueLiteralBaseEquiv emb).symm.trans
    ((glueStressEquiv (glueSeams emb hd) hd).trans (glueLiteralGroundEquiv emb))

theorem glue_literal_rank_two (emb : GlueV d ↪ Fin n) (hd : 5 ≤ d) :
    Module.finrank F (literalStress (d := d) (glueGround emb)) = 2 :=
  ((glueParameterEquiv emb hd).trans (glueLiteralGroundEquiv emb)).finrank_eq.symm.trans
    (glue_parameter_dim emb)

theorem glue_fin_witness (d n : ℕ) (hd : 5 ≤ d) (hodd : Odd d)
    (hn : 2*(d+2)^2 + 2*(d+2) - 1 ≤ n) :
    let emb := glueEmbedding d n hn
    let D := glueGround emb
    let H := gluePairFamily emb hodd
    (⋃₀ H) = D ∧ H.PairwiseDisjoint id ∧ (∀ P ∈ H, P.ncard = 2) ∧
      H.ncard = (d+3)*((d+2)^2+(d+2)-2)/2 ∧
      genericRank (D := Fin d) D = (d+3)*((d+2)^2+(d+2)-2)-2 ∧
      (∀ P ∈ H, genericRank (D := Fin d) (D \ P) = (d+3)*((d+2)^2+(d+2)-2)-3) ∧
      ∀ e : Edge (Fin n), e ∉ D → ∃ P ∈ H, genericRow (D := Fin d) e ∉ glueSpan (D \ P) := by
  dsimp only
  let emb := glueEmbedding d n hn
  refine ⟨glue_pairs_cover emb hodd, glue_pair_family_disjoint emb hodd,
    fun _ h => glue_pair_family_two emb hodd h, glue_pair_family_card emb hodd,
    glue_ground_rank emb hd, ?_, glue_ambient_fin d n hd hodd hn⟩
  rintro _ ⟨t,rfl⟩
  exact glue_pair_deletion_rank emb hd hodd t

#print axioms glueLiteralBaseEquiv
#print axioms glueLiteralGroundEquiv
#print axioms glueLiteralStressEquiv
#print axioms glue_literal_rank_two
#print axioms glue_fin_witness

end
end Rigidity369952
```

## GlueSignatures.lean

```lean
import GlueLiteral

namespace Rigidity369952

#eval Lean.versionString

#check genericRank
#print axioms genericRank

#check GenericIndependent
#print axioms GenericIndependent

#check real_independent_iff
#print axioms real_independent_iff

#check generic_Kss
#print axioms generic_Kss

#check generic_Kssplus1
#print axioms generic_Kssplus1

#check generic_Kssplus1_double_circuit
#print axioms generic_Kssplus1_double_circuit

#check generic_Kss_seam_expansion
#print axioms generic_Kss_seam_expansion

#check generic_two_vertex_seam
#print axioms generic_two_vertex_seam

#check Kss_same_side_generic_separation
#print axioms Kss_same_side_generic_separation

#check GlueS
#print axioms GlueS

#check GlueJ
#print axioms GlueJ

#check GlueT
#print axioms GlueT

#check GlueV
#print axioms GlueV

#check glueBaseLabel
#print axioms glueBaseLabel

#check glueLocalLeft
#print axioms glueLocalLeft

#check glueLocalRight
#print axioms glueLocalRight

#check glueLocalLeft_injective
#print axioms glueLocalLeft_injective

#check glueLocalRight_injective
#print axioms glueLocalRight_injective

#check glueLocalLabel
#print axioms glueLocalLabel

#check glueV_card
#print axioms glueV_card

#check glueEmbedding
#print axioms glueEmbedding

#check glueBase
#print axioms glueBase

#check glueLocal
#print axioms glueLocal

#check GlueLocalEdge
#print axioms GlueLocalEdge

#check GlueClass
#print axioms GlueClass

#check GlueIndex
#print axioms GlueIndex

#check glueEdge
#print axioms glueEdge

#check glueGround
#print axioms glueGround

#check glueColumn
#print axioms glueColumn

#check glueRightCol
#print axioms glueRightCol

#check glueColumn_injective
#print axioms glueColumn_injective

#check glueColumn_right
#print axioms glueColumn_right

#check glueEdge_eq_bipEdge
#print axioms glueEdge_eq_bipEdge

#check glueEdge_injective
#print axioms glueEdge_injective

#check glueLocalLeft_case
#print axioms glueLocalLeft_case

#check glueLocalRight_case
#print axioms glueLocalRight_case

#check glueInternal
#print axioms glueInternal

#check glueLocalLabel_cases
#print axioms glueLocalLabel_cases

#check glueInternal_unique
#print axioms glueInternal_unique

#check glueRows
#print axioms glueRows

#check glueRetainedForce
#print axioms glueRetainedForce

#check glueGadgetForce
#print axioms glueGadgetForce

#check glue_sum
#print axioms glue_sum

#check glueAssemble
#print axioms glueAssemble

#check glue_assemble_sum
#print axioms glue_assemble_sum

#check crossRows_zero_of_other_vertex
#print axioms crossRows_zero_of_other_vertex

#check IsGlueInternal
#print axioms IsGlueInternal

#check glue_internal_not_base
#print axioms glue_internal_not_base

#check glue_internal_unique
#print axioms glue_internal_unique

#check glue_local_vertex_cases
#print axioms glue_local_vertex_cases

#check glue_gadget_force_zero
#print axioms glue_gadget_force_zero

#check glue_retained_force_zero
#print axioms glue_retained_force_zero

#check glue_force_at_internal
#print axioms glue_force_at_internal

#check glue_gadget_recompress
#print axioms glue_gadget_recompress

#check GlueSeams
#print axioms GlueSeams

#check glueSeams
#print axioms glueSeams

#check glue_gadget_factor
#print axioms glue_gadget_factor

#check glueExpand
#print axioms glueExpand

#check glue_expand_sums
#print axioms glue_expand_sums

#check glueStressMap
#print axioms glueStressMap

#check glue_stress_injective
#print axioms glue_stress_injective

#check glue_stress_surjective
#print axioms glue_stress_surjective

#check glueStressEquiv
#print axioms glueStressEquiv

#check GlueParameters
#print axioms GlueParameters

#check glue_parameter_dim
#print axioms glue_parameter_dim

#check glue_parameter_two_zero
#print axioms glue_parameter_two_zero

#check glue_coordinate_surjective
#print axioms glue_coordinate_surjective

#check glue_coordinate_kernel_rank
#print axioms glue_coordinate_kernel_rank

#check glueLambda
#print axioms glueLambda

#check glueLambda_rel
#print axioms glueLambda_rel

#check glueLambda_ne
#print axioms glueLambda_ne

#check glueBaseMap
#print axioms glueBaseMap

#check glueBaseEquiv
#print axioms glueBaseEquiv

#check glueParameterEquiv
#print axioms glueParameterEquiv

#check glueWeight
#print axioms glueWeight

#check glueWeight_ne
#print axioms glueWeight_ne

#check glue_factor
#print axioms glue_factor

#check glue_stress_zero_iff
#print axioms glue_stress_zero_iff

#check glue_stress_two_class_zero
#print axioms glue_stress_two_class_zero

#check zeroExtend
#print axioms zeroExtend

#check supported_sum
#print axioms supported_sum

#check supportedRelations
#print axioms supportedRelations

#check restrictStressEquiv
#print axioms restrictStressEquiv

#check glueSubset
#print axioms glueSubset

#check glue_mem_subset
#print axioms glue_mem_subset

#check glueSubsetEquiv
#print axioms glueSubsetEquiv

#check glueAllowedParameters
#print axioms glueAllowedParameters

#check glueRestrictedParameters
#print axioms glueRestrictedParameters

#check glue_subset_rank_add
#print axioms glue_subset_rank_add

#check glueDelete
#print axioms glueDelete

#check glue_delete_eq
#print axioms glue_delete_eq

#check glue_class_card
#print axioms glue_class_card

#check glue_ground_rank
#print axioms glue_ground_rank

#check glue_allowed_same
#print axioms glue_allowed_same

#check glue_allowed_cross
#print axioms glue_allowed_cross

#check glue_delete_same_rank
#print axioms glue_delete_same_rank

#check glue_delete_cross_rank
#print axioms glue_delete_cross_rank

#check glueClassSet
#print axioms glueClassSet

#check glueClassEquiv
#print axioms glueClassEquiv

#check glue_class_rank
#print axioms glue_class_rank

#check glue_class_complement_rank
#print axioms glue_class_complement_rank

#check GluePairKind
#print axioms GluePairKind

#check GluePairName
#print axioms GluePairName

#check glueHalfEquiv
#print axioms glueHalfEquiv

#check glueCrossGadget
#print axioms glueCrossGadget

#check glueExtraGadget
#print axioms glueExtraGadget

#check gluePairClass
#print axioms gluePairClass

#check gluePairClass_injective
#print axioms gluePairClass_injective

#check gluePairClass_surjective
#print axioms gluePairClass_surjective

#check gluePairIndex
#print axioms gluePairIndex

#check gluePairIndex_bijective
#print axioms gluePairIndex_bijective

#check gluePair
#print axioms gluePair

#check gluePairFamily
#print axioms gluePairFamily

#check glue_pair_cross
#print axioms glue_pair_cross

#check glue_pair_disjoint
#print axioms glue_pair_disjoint

#check glue_pair_two
#print axioms glue_pair_two

#check glue_pairs_cover
#print axioms glue_pairs_cover

#check glueSpan
#print axioms glueSpan

#check glueSynthesis
#print axioms glueSynthesis

#check glue_span_iff
#print axioms glue_span_iff

#check glueNormalized
#print axioms glueNormalized

#check glue_normalized_difference
#print axioms glue_normalized_difference

#check glue_normalized_iff_delete
#print axioms glue_normalized_iff_delete

#check ambientEdge
#print axioms ambientEdge

#check ambientEdge_swap
#print axioms ambientEdge_swap

#check generic_position_ne
#print axioms generic_position_ne

#check generic_edge_at_left
#print axioms generic_edge_at_left

#check generic_edge_at_right
#print axioms generic_edge_at_right

#check generic_edge_zero
#print axioms generic_edge_zero

#check glue_synthesis_mem
#print axioms glue_synthesis_mem

#check glue_synthesis_of_mem
#print axioms glue_synthesis_of_mem

#check glue_deleted_span_le
#print axioms glue_deleted_span_le

#check glue_synthesis_zero_unused
#print axioms glue_synthesis_zero_unused

#check glue_unused_not_mem
#print axioms glue_unused_not_mem

#check glue_gadget_force_mem
#print axioms glue_gadget_force_mem

#check glue_gadget_force_mem_ground
#print axioms glue_gadget_force_mem_ground

#check glue_recompress_outside
#print axioms glue_recompress_outside

#check glue_same_side_not_mem
#print axioms glue_same_side_not_mem

#check base_force_left
#print axioms base_force_left

#check base_force_right
#print axioms base_force_right

#check glue_base_recompression
#print axioms glue_base_recompression

#check glue_base_edge_separation
#print axioms glue_base_edge_separation

#check glueProject
#print axioms glueProject

#check glueSkew
#print axioms glueSkew

#check glueGram
#print axioms glueGram

#check glueProject_orthogonal
#print axioms glueProject_orthogonal

#check glueSkew_sub
#print axioms glueSkew_sub

#check glueSkew_zero
#print axioms glueSkew_zero

#check glueSkew_diagonal
#print axioms glueSkew_diagonal

#check glueGram_eq_motion
#print axioms glueGram_eq_motion

#check glue_gram_projected
#print axioms glue_gram_projected

#check glue_map_dot
#print axioms glue_map_dot

#check glue_map_project
#print axioms glue_map_project

#check glue_map_gram
#print axioms glue_map_gram

#check glue_generic_gram_nonzero
#print axioms glue_generic_gram_nonzero

#check glue_internal_mem_local
#print axioms glue_internal_mem_local

#check glueOffset
#print axioms glueOffset

#check glueOffset_sub
#print axioms glueOffset_sub

#check glueMotion
#print axioms glueMotion

#check glueMotion_on_local
#print axioms glueMotion_on_local

#check glueWork
#print axioms glueWork

#check glue_work_edge
#print axioms glue_work_edge

#check glue_cross_gadget_separation
#print axioms glue_cross_gadget_separation

#check glueSeamSet
#print axioms glueSeamSet

#check glue_deleted_seam
#print axioms glue_deleted_seam

#check glue_ground_literal
#print axioms glue_ground_literal

#check glue_used_base_or_internal
#print axioms glue_used_base_or_internal

#check glue_internal_edge_separation
#print axioms glue_internal_edge_separation

#check glue_ambient_separation
#print axioms glue_ambient_separation

#check glue_ambient_family_separation
#print axioms glue_ambient_family_separation

#check glue_ambient_fin
#print axioms glue_ambient_fin

#check glue_local_base_labels
#print axioms glue_local_base_labels

#check glue_internal_disjoint
#print axioms glue_internal_disjoint

#check glue_pair_family_disjoint
#print axioms glue_pair_family_disjoint

#check glue_pair_family_two
#print axioms glue_pair_family_two

#check glue_pair_family_card
#print axioms glue_pair_family_card

#check glue_exact_column_support
#print axioms glue_exact_column_support

#check glue_column_classes
#print axioms glue_column_classes

#check glue_pair_deletion_rank
#print axioms glue_pair_deletion_rank

#check relationSpaceReindex
#print axioms relationSpaceReindex

#check literalStress
#print axioms literalStress

#check glueLiteralBaseEquiv
#print axioms glueLiteralBaseEquiv

#check glueLiteralGroundEquiv
#print axioms glueLiteralGroundEquiv

#check glueLiteralStressEquiv
#print axioms glueLiteralStressEquiv

#check glue_literal_rank_two
#print axioms glue_literal_rank_two

#check glue_fin_witness
#print axioms glue_fin_witness

end Rigidity369952
```

## MatchingRank.lean

```lean
import GlueSignatures
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators

namespace Rigidity369952

noncomputable section
namespace Matching

variable {E K V : Type*} [DecidableEq E] [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]

def rowSpan (x : E → V) (A : Finset E) :=
  Submodule.span K (x '' (A : Set E))

def rowRank (x : E → V) (A : Finset E) :=
  Module.finrank K (rowSpan (K := K) x A)

local notation "ρ" => rowRank (K := K)

omit [DecidableEq E] in
theorem rank_mono (x : E → V) {A B : Finset E} (h : A ⊆ B) :
    ρ x A ≤ ρ x B :=
  Submodule.finrank_mono (Submodule.span_mono (Set.image_mono h))

omit [DecidableEq E] [Module.Finite K V] in
@[simp] theorem rank_empty (x : E → V) : ρ x ∅ = 0 := by
  unfold rowRank rowSpan
  have he : x '' ((∅ : Finset E) : Set E) = ∅ := by ext e; simp
  rw [he, Submodule.span_empty, finrank_bot]

omit [DecidableEq E] [Module.Finite K V] in
theorem rank_card (x : E → V) (A : Finset E) : ρ x A ≤ A.card := by
  classical
  have h := finrank_span_finset_le_card (R := K) (A.image x)
  rw [Finset.coe_image] at h
  exact h.trans Finset.card_image_le

omit [Module.Finite K V] in
theorem span_union (x : E → V) (A B : Finset E) :
    rowSpan (K := K) x (A ∪ B) = rowSpan x A ⊔ rowSpan x B := by
  simp [rowSpan, Set.image_union, Submodule.span_union]

theorem rank_submod (x : E → V) (A B : Finset E) :
    ρ x (A ∪ B) + ρ x (A ∩ B) ≤ ρ x A + ρ x B := by
  have h : rowSpan (K := K) x (A ∩ B) ≤ rowSpan x A ⊓ rowSpan x B :=
    le_inf (Submodule.span_mono (Set.image_mono Finset.inter_subset_left))
      (Submodule.span_mono (Set.image_mono Finset.inter_subset_right))
  have he := Submodule.finrank_sup_add_finrank_inf_eq (rowSpan (K := K) x A) (rowSpan x B)
  unfold rowRank
  rw [span_union]
  exact (Nat.add_le_add_left (Submodule.finrank_mono h) _).trans_eq he

theorem rank_insert_le (x : E → V) (e : E) (A : Finset E) :
    ρ x (insert e A) ≤ ρ x A + 1 := by
  have h := rank_submod (K := K) x ({e} : Finset E) A
  have he := rank_card (K := K) x ({e} : Finset E)
  rw [Finset.card_singleton] at he
  simp only [Finset.singleton_union] at h
  omega

theorem rank_insert_of_outside (x : E → V) (e : E) (A : Finset E)
    (he : x e ∉ rowSpan (K := K) x A) :
    ρ x (insert e A) = ρ x A + 1 := by
  have hle : rowSpan (K := K) x A ≤ rowSpan x (insert e A) :=
    Submodule.span_mono (Set.image_mono (Finset.subset_insert e A))
  have hm : x e ∈ rowSpan (K := K) x (insert e A) :=
    Submodule.subset_span ⟨e, Finset.mem_insert_self _ _, rfl⟩
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hle (fun h => he (h hm)))
  have hu := rank_insert_le (K := K) x e A
  change ρ x A < ρ x (insert e A) at hlt
  omega

def IsFlat (r : Finset E → ℕ) (Z : Finset E) : Prop :=
  ∀ e, r (insert e Z) = r Z ↔ e ∈ Z

def ground (H : Finset (Finset E)) : Finset E := H.biUnion id

def IsPartition (H : Finset (Finset E)) (π : Finset (Finset (Finset E))) : Prop :=
  (∀ B ∈ π, B.Nonempty) ∧ (π : Set (Finset (Finset E))).PairwiseDisjoint id ∧
    π.biUnion id = H

def IsMatching (r : Finset E → ℕ) (H J : Finset (Finset E)) : Prop :=
  J ⊆ H ∧ r (ground J) = 2 * J.card

def value (r : Finset E → ℕ) (Z : Finset E) (π : Finset (Finset (Finset E))) : ℕ :=
  r Z + ∑ B ∈ π, (r (Z ∪ ground B) - r Z) / 2

def MatchSizes (r : Finset E → ℕ) (H : Finset (Finset E)) : Set ℕ :=
  {v | ∃ J, IsMatching r H J ∧ J.card = v}

def CoverValues (r : Finset E → ℕ) (H : Finset (Finset E)) : Set ℕ :=
  {v | ∃ Z π, IsFlat r Z ∧ IsPartition H π ∧ value r Z π = v}

def HasMatchingProperty (r : Finset E → ℕ) : Prop :=
  ∀ H : Finset (Finset E), (∀ P ∈ H, P.card = 2) →
    ∃ a, IsGreatest (MatchSizes r H) a ∧ IsLeast (CoverValues r H) a

#print axioms rank_submod
#print axioms rank_insert_of_outside

end Matching
end
end Rigidity369952
```

## MatchingUpper.lean

```lean
import MatchingRank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace Rigidity369952.Matching

noncomputable section

variable {E K V : Type*} [DecidableEq E] [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]

local notation "ρ" => rowRank (K := K)

theorem ground_mono {H J : Finset (Finset E)} (h : J ⊆ H) : ground J ⊆ ground H := by
  intro e he
  obtain ⟨P,hP,heP⟩ := Finset.mem_biUnion.mp he
  exact Finset.mem_biUnion.mpr ⟨P,h hP,heP⟩

theorem ground_card_le {H : Finset (Finset E)} (h : ∀ P ∈ H, P.card = 2) :
    (ground H).card ≤ 2 * H.card := by
  unfold ground
  calc
    _ ≤ ∑ P ∈ H, P.card := Finset.card_biUnion_le
    _ = ∑ _P ∈ H, 2 := Finset.sum_congr rfl (fun P hP => h P hP)
    _ = _ := by simp [Nat.mul_comm]

theorem ground_card {H : Finset (Finset E)} (h : ∀ P ∈ H, P.card = 2)
    (hd : (H : Set (Finset E)).PairwiseDisjoint id) : (ground H).card = 2 * H.card := by
  unfold ground
  rw [Finset.card_biUnion hd]
  calc
    _ = ∑ _P ∈ H, 2 := Finset.sum_congr rfl (fun P hP => h P hP)
    _ = _ := by simp [Nat.mul_comm]

omit [Module.Finite K V] in
theorem selected_disjoint (x : E → V) {H J : Finset (Finset E)}
    (hp : ∀ P ∈ H, P.card = 2) (h : IsMatching (ρ x) H J) :
    (J : Set (Finset E)).PairwiseDisjoint id := by
  classical
  have hc : (ground J).card = 2 * J.card := le_antisymm
    (ground_card_le (fun P hP => hp P (h.1 hP))) (h.2 ▸ rank_card x (ground J))
  have hpJ : ∀ P ∈ J, P.card = 2 := fun P hP => hp P (h.1 hP)
  clear x h hp
  induction J using Finset.induction_on with
  | empty => simp
  | @insert P J hPJ ih =>
    have hm : ground (insert P J) = P ∪ ground J := by simp [ground]
    have hc' := Finset.card_union_add_card_inter P (ground J)
    have hl := ground_card_le (H := J) (fun Q hQ => hpJ Q (Finset.subset_insert P J hQ))
    have hP := hpJ P (Finset.mem_insert_self _ _)
    rw [hm, Finset.card_insert_of_notMem hPJ] at hc
    have hi : (P ∩ ground J).card = 0 := by omega
    have hd : Disjoint P (ground J) := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hi)
    have hJ := ih (by omega) (fun Q hQ => hpJ Q (Finset.subset_insert P J hQ))
    intro Q hQ R hR hne
    change Q ∈ insert P J at hQ
    change R ∈ insert P J at hR
    rcases Finset.mem_insert.mp hQ with rfl | hQ'
    · have hR' := (Finset.mem_insert.mp hR).resolve_left (Ne.symm hne)
      have hsub : R ⊆ ground J := fun e he => Finset.mem_biUnion.mpr ⟨R,hR',he⟩
      exact hd.mono_right hsub
    · rcases Finset.mem_insert.mp hR with rfl | hR'
      · have hsub : Q ⊆ ground J := fun e he => Finset.mem_biUnion.mpr ⟨Q,hQ',he⟩
        exact hd.symm.mono_left hsub
      · exact hJ hQ' hR' hne

theorem increment_le (x : E → V) (Z A : Finset E) :
    ρ x (Z ∪ A) - ρ x Z ≤ ρ x A := by
  have := rank_submod (K := K) x Z A
  omega

theorem increment_union (x : E → V) (Z A B : Finset E) :
    ρ x (Z ∪ (A ∪ B)) - ρ x Z ≤
      (ρ x (Z ∪ A) - ρ x Z) + (ρ x (Z ∪ B) - ρ x Z) := by
  have h := rank_submod (K := K) x (Z ∪ A) (Z ∪ B)
  have ha := rank_mono (K := K) x (Finset.subset_union_left (s₁ := Z) (s₂ := A))
  have hb := rank_mono (K := K) x (Finset.subset_union_left (s₁ := Z) (s₂ := B))
  have hi := rank_mono (K := K) x (Finset.subset_inter Finset.subset_union_left Finset.subset_union_left :
    Z ⊆ (Z ∪ A) ∩ (Z ∪ B))
  have he : (Z ∪ A) ∪ (Z ∪ B) = Z ∪ (A ∪ B) := by
    ext e
    simp only [Finset.mem_union]
    tauto
  rw [he] at h
  omega

theorem increment_biUnion (x : E → V) (Z : Finset E) {ι : Type*} (s : Finset ι)
    (f : ι → Finset E) :
    ρ x (Z ∪ s.biUnion f) - ρ x Z ≤ ∑ i ∈ s, (ρ x (Z ∪ f i) - ρ x Z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (increment_union x Z _ _).trans (Nat.add_le_add_left ih _)

theorem pieces_cover {H J : Finset (Finset E)} {π : Finset (Finset (Finset E))}
    (hc : π.biUnion id = H) (hj : J ⊆ H) :
    π.biUnion (fun B => J ∩ B) = J := by
  ext P
  constructor
  · intro h
    obtain ⟨B,_,hB⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_inter.mp hB).1
  · intro h
    have hm : P ∈ π.biUnion id := hc ▸ hj h
    obtain ⟨B,hB,hP⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨B,hB,Finset.mem_inter.mpr ⟨h,hP⟩⟩

theorem pieces_count {H J : Finset (Finset E)} {π : Finset (Finset (Finset E))}
    (hp : IsPartition H π) (hj : J ⊆ H) :
    (∑ B ∈ π, (J ∩ B).card) = J.card := by
  have hd : (π : Set (Finset (Finset E))).PairwiseDisjoint (fun B => J ∩ B) := by
    intro A hA B hB hab
    exact (hp.2.1 hA hB hab).mono Finset.inter_subset_right Finset.inter_subset_right
  rw [← Finset.card_biUnion hd, pieces_cover hp.2.2 hj]

theorem ground_pieces (π : Finset (Finset (Finset E))) (J : Finset (Finset E)) :
    π.biUnion (fun B => ground (J ∩ B)) = ground (π.biUnion (fun B => J ∩ B)) := by
  ext e
  simp only [ground, Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨B,hB,P,hP,he⟩
    exact ⟨P,⟨B,hB,hP⟩,he⟩
  · rintro ⟨P,⟨B,hB,hP⟩,he⟩
    exact ⟨B,hB,P,hP,he⟩

theorem matching_upper (x : E → V) {H J : Finset (Finset E)}
    (hp : ∀ P ∈ H, P.card = 2) (hj : IsMatching (ρ x) H J)
    (Z : Finset E) {π : Finset (Finset (Finset E))} (hπ : IsPartition H π) :
    J.card ≤ value (ρ x) Z π := by
  let q (B : Finset (Finset E)) := (J ∩ B).card
  let a (B : Finset (Finset E)) := ρ x (Z ∪ ground (J ∩ B)) - ρ x Z
  let L B := 2 * q B - a B
  have ha (B) : a B ≤ 2 * q B := (increment_le x Z _).trans
    ((rank_card x _).trans (ground_card_le (fun P hP => hp P (hj.1 (Finset.mem_inter.mp hP).1))))
  have hsum : (∑ B ∈ π, a B) + (∑ B ∈ π, L B) = 2 * J.card := by
    calc
      _ = ∑ B ∈ π, (a B + L B) := Finset.sum_add_distrib.symm
      _ = ∑ B ∈ π, 2 * q B := Finset.sum_congr rfl (fun B _ => by
        have := ha B
        dsimp only [L]
        omega)
      _ = _ := by rw [← Finset.mul_sum]; exact congrArg (2 * ·) (pieces_count hπ hj.1)
  have ht := increment_biUnion (K := K) x Z π (fun B => ground (J ∩ B))
  rw [ground_pieces, pieces_cover hπ.2.2 hj.1] at ht
  have hm := rank_mono (K := K) x (Finset.subset_union_right (s₁ := Z) (s₂ := ground J))
  change ρ x (Z ∪ ground J) - ρ x Z ≤ ∑ B ∈ π, a B at ht
  have hL : (∑ B ∈ π, L B) ≤ ρ x Z := by
    rw [hj.2] at hm
    omega
  have hterm (B) : q B ≤ (ρ x (Z ∪ ground B) - ρ x Z) / 2 + L B := by
    have hsub : Z ∪ ground (J ∩ B) ⊆ Z ∪ ground B :=
      Finset.union_subset_union Finset.Subset.rfl (ground_mono Finset.inter_subset_right)
    have hmono := rank_mono (K := K) x hsub
    have hq := ha B
    dsimp only [L, a] at *
    omega
  have htotal := Finset.sum_le_sum (s := π) (fun B _ => hterm B)
  rw [Finset.sum_add_distrib] at htotal
  change (∑ B ∈ π, (J ∩ B).card) ≤ _ at htotal
  rw [pieces_count hπ hj.1] at htotal
  unfold value
  omega

#print axioms selected_disjoint
#print axioms matching_upper

end
end Rigidity369952.Matching
```

## MatchingInside.lean

```lean
import MatchingUpper

open scoped BigOperators

namespace Rigidity369952.Matching

noncomputable section

variable {E : Type*} [DecidableEq E]

theorem block_subset {H : Finset (Finset E)} {π : Finset (Finset (Finset E))}
    (hπ : IsPartition H π) {B : Finset (Finset E)} (hB : B ∈ π) : B ⊆ H := by
  intro P hp
  rw [← hπ.2.2]
  exact Finset.mem_biUnion.mpr ⟨B,hB,hp⟩

theorem block_size_sum {H : Finset (Finset E)} {π : Finset (Finset (Finset E))}
    (hπ : IsPartition H π) : (∑ B ∈ π, B.card) = H.card := by
  have h := Finset.card_biUnion hπ.2.1
  rw [hπ.2.2] at h
  exact h.symm

theorem block_inter_sum {H : Finset (Finset E)} {π : Finset (Finset (Finset E))}
    (hπ : IsPartition H π) (hd : (H : Set (Finset E)).PairwiseDisjoint id)
    (Z : Finset E) (hz : Z ⊆ ground H) :
    (∑ B ∈ π, (Z ∩ ground B).card) = Z.card := by
  have hdis : (π : Set (Finset (Finset E))).PairwiseDisjoint (fun B => Z ∩ ground B) := by
    intro A ha B hb hab
    apply Finset.disjoint_left.mpr
    intro e hea heb
    obtain ⟨P,hP,heP⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hea).2
    obtain ⟨Q,hQ,heQ⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp heb).2
    by_cases hpq : P = Q
    · subst Q
      exact Finset.disjoint_left.mp (hπ.2.1 ha hb hab) hP hQ
    · exact Finset.disjoint_left.mp (hd (block_subset hπ ha hP) (block_subset hπ hb hQ) hpq) heP heQ
  rw [← Finset.card_biUnion hdis]
  congr 1
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · rintro ⟨_,_,he,_⟩
    exact he
  · intro he
    obtain ⟨P,hP,heP⟩ := Finset.mem_biUnion.mp (hz he)
    rw [← hπ.2.2] at hP
    obtain ⟨B,hB,hPB⟩ := Finset.mem_biUnion.mp hP
    exact ⟨B,hB,he,Finset.mem_biUnion.mpr ⟨P,hPB,heP⟩⟩

theorem inside_lower (r : Finset E → ℕ) {H : Finset (Finset E)}
    (hp : ∀ P ∈ H, P.card = 2) (hd : (H : Set (Finset E)).PairwiseDisjoint id)
    {π : Finset (Finset (Finset E))} (hπ : IsPartition H π)
    (Z : Finset E) (hz : Z ⊆ ground H) (C : ℕ) (hC : H.card + 1 ≤ C)
    (hr : ∀ A ⊆ ground H, r A ≤ A.card)
    (hn : ∀ A ⊆ ground H, A.card ≤ r A + 2)
    (hc : ∀ A ⊆ ground H, r A < A.card → C - 1 ≤ r A) :
    H.card - 1 ≤ value r Z π := by
  classical
  by_contra! hlt
  have hri : r Z = Z.card := by
    have h0 : r Z ≤ value r Z π := by unfold value; omega
    by_contra hne
    have := hc Z hz (lt_of_le_of_ne (hr Z hz) hne)
    omega
  let a (B : Finset (Finset E)) := (r (Z ∪ ground B) - r Z) / 2
  let t (B : Finset (Finset E)) := (Z ∩ ground B).card
  let bad := π.filter (fun B => r (Z ∪ ground B) < (Z ∪ ground B).card)
  have hsub B (hB : B ∈ π) : Z ∪ ground B ⊆ ground H :=
    Finset.union_subset hz (ground_mono (block_subset hπ hB))
  have hbig B (hB : B ∈ bad) : (C - 1 - r Z) / 2 ≤ a B := by
    have hb := Finset.mem_filter.mp hB
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (hc _ (hsub B hb.1) hb.2) _)
  by_cases hbad : bad.card ≤ 1
  · have hterm B (hB : B ∈ π) : B.card ≤ a B + t B + (if B ∈ bad then 1 else 0) := by
      have hcard : (ground B).card = 2 * B.card :=
        ground_card (fun P hP => hp P (block_subset hπ hB hP))
          (fun _ hP _ hQ hne => hd (block_subset hπ hB hP) (block_subset hπ hB hQ) hne)
      have hu := Finset.card_union_add_card_inter Z (ground B)
      have hn' := hn _ (hsub B hB)
      have hr' := hr _ (hsub B hB)
      unfold a t
      split
      · omega
      · rename_i hnot
        have hib : ¬ r (Z ∪ ground B) < (Z ∪ ground B).card :=
          fun h => hnot (Finset.mem_filter.mpr ⟨hB,h⟩)
        omega
    have hsum := Finset.sum_le_sum (s := π) hterm
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, block_size_sum hπ] at hsum
    change H.card ≤ (∑ B ∈ π, a B) + (∑ B ∈ π, (Z ∩ ground B).card) + _ at hsum
    rw [block_inter_sum hπ hd Z hz] at hsum
    have hcount : (∑ B ∈ π, if B ∈ bad then (1 : ℕ) else 0) = bad.card := by
      rw [← Finset.sum_filter]
      have he : π.filter (· ∈ bad) = bad :=
        by
        ext B
        exact ⟨fun h => (Finset.mem_filter.mp h).2,
          fun h => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,h⟩⟩
      rw [he]
      simp
    rw [hcount] at hsum
    have hbound : H.card ≤ value r Z π + bad.card := by
      change H.card ≤ (r Z + ∑ B ∈ π, a B) + bad.card
      omega
    by_cases hnone : bad.card = 0
    · have hall : H.card ≤ value r Z π := by omega
      omega
    · have hone : bad.card = 1 := by omega
      have hlower : H.card - 1 ≤ value r Z π := by omega
      omega
  · have ht : 1 < bad.card := by omega
    obtain ⟨B,F,hB,hF,hne⟩ := Finset.one_lt_card_iff.mp ht
    have hBF : ({B,F} : Finset _) ⊆ π := by
      intro G hG
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact (Finset.mem_filter.mp hB).1
      · obtain rfl := Finset.mem_singleton.mp hG
        exact (Finset.mem_filter.mp hF).1
    have hs : a B + a F ≤ ∑ G ∈ π, a G := by
      simpa [Finset.sum_pair hne] using Finset.sum_le_sum_of_subset_of_nonneg hBF
        (fun G _ _ => Nat.zero_le (a G))
    have hb := hbig B hB
    have hf := hbig F hF
    have hlower : C - 2 ≤ value r Z π := by
      change C - 2 ≤ r Z + ∑ G ∈ π, a G
      omega
    omega

#print axioms inside_lower

end
end Rigidity369952.Matching
```

## MatchingOutside.lean

```lean
import MatchingInside

open scoped BigOperators

namespace Rigidity369952.Matching

noncomputable section

variable {E K V : Type*} [DecidableEq E] [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]

local notation "ρ" => rowRank (K := K)

theorem ground_erase {H : Finset (Finset E)}
    (hd : (H : Set (Finset E)).PairwiseDisjoint id) {P : Finset E} (hP : P ∈ H) :
    ground (H.erase P) = ground H \ P := by
  ext e
  simp only [ground, Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_erase, id_eq]
  constructor
  · rintro ⟨Q,⟨hne,hQ⟩,heQ⟩
    exact ⟨⟨Q,hQ,heQ⟩, fun heP => Finset.disjoint_left.mp (hd hQ hP hne) heQ heP⟩
  · rintro ⟨⟨Q,hQ,heQ⟩,heP⟩
    exact ⟨Q,⟨fun h => heP (h ▸ heQ),hQ⟩,heQ⟩

theorem ground_erase_two {H : Finset (Finset E)}
    (hd : (H : Set (Finset E)).PairwiseDisjoint id) {P Q : Finset E}
    (hP : P ∈ H) (hQ : Q ∈ H) (hPQ : P ≠ Q) :
    ground ((H.erase P).erase Q) = (ground H \ P) \ Q := by
  rw [ground_erase
    (fun _ ha _ hb hne => hd (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hne)
    (Finset.mem_erase.mpr ⟨Ne.symm hPQ,hQ⟩), ground_erase hd hP]

theorem augment_partition {H : Finset (Finset E)} {π : Finset (Finset (Finset E))}
    (hπ : IsPartition H π) {P : Finset E} (hP : P ∉ H) :
    IsPartition (insert P H) (insert {P} π) := by
  refine ⟨?_,?_,?_⟩
  · intro B hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact Finset.singleton_nonempty _
    · exact hπ.1 B hb
  · intro A hA B hB hne
    change A ∈ insert {P} π at hA
    change B ∈ insert {P} π at hB
    rcases Finset.mem_insert.mp hA with rfl | hA'
    · have hb := (Finset.mem_insert.mp hB).resolve_left (Ne.symm hne)
      exact Finset.disjoint_left.mpr (fun Q hm hq => hP ((Finset.mem_singleton.mp hm) ▸ block_subset hπ hb hq))
    · rcases Finset.mem_insert.mp hB with rfl | hB'
      · exact Finset.disjoint_left.mpr (fun Q hq hm => hP ((Finset.mem_singleton.mp hm) ▸ block_subset hπ hA' hq))
      · exact hπ.2.1 hA' hB' hne
  · rw [Finset.biUnion_insert, hπ.2.2]
    change {P} ∪ H = insert P H
    ext Q
    simp

theorem outside_auxiliary (x : E → V) {H : Finset (Finset E)}
    (hp : ∀ P ∈ H, P.card = 2) (hd : (H : Set (Finset E)).PairwiseDisjoint id)
    {Z : Finset E} {π : Finset (Finset (Finset E))} (hπ : IsPartition H π)
    {e f g : E} {P Q : Finset E} (heZ : e ∈ Z) (heD : e ∉ ground H)
    (hP : P ∈ H) (hQ : Q ∈ H) (hpq : P ≠ Q)
    (hq : Q = {f,g}) (hfg : f ≠ g)
    (hind : ρ x ((ground H \ P) \ {g}) = 2 * H.card - 3)
    (hsep : x e ∉ rowSpan (K := K) x (ground H \ P)) :
    H.card - 1 ≤ value (ρ x) Z π := by
  classical
  let T : Finset E := {e,f}
  let J := (H.erase P).erase Q
  have hfQ : f ∈ Q := by simp [hq]
  have hfD : f ∈ ground H := Finset.mem_biUnion.mpr ⟨Q,hQ,hfQ⟩
  have hef : e ≠ f := fun h => heD (h ▸ hfD)
  have hT : T ∉ H := fun h => heD (Finset.mem_biUnion.mpr ⟨T,h,Finset.mem_insert_self _ _⟩)
  have hTD : T.card = 2 := by simp [T,hef]
  have hπT : ({T} : Finset (Finset E)) ∉ π :=
    fun h => hT (block_subset hπ h (Finset.mem_singleton_self T))
  have hJ : J ⊆ H := fun _ h => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
  have hTJ : T ∉ J := fun h => hT (hJ h)
  have hqP : Q ∈ H.erase P := Finset.mem_erase.mpr ⟨Ne.symm hpq,hQ⟩
  have hcardJ : J.card = H.card - 2 := by
    unfold J
    rw [Finset.card_erase_of_mem hqP, Finset.card_erase_of_mem hP]
    omega
  have hh : 2 ≤ H.card := by
    have h := Finset.card_pos.mpr ⟨Q,hqP⟩
    rw [Finset.card_erase_of_mem hP] at h
    omega
  have hfP : f ∉ P := fun h => Finset.disjoint_left.mp (hd hP hQ hpq) h hfQ
  have hu : ground (insert T J) = insert e ((ground H \ P) \ {g}) := by
    unfold J
    rw [show ground (insert T ((H.erase P).erase Q)) = T ∪ ground ((H.erase P).erase Q) by simp [ground],
      ground_erase_two hd hP hQ hpq, hq]
    ext a
    simp only [T, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff]
    by_cases ha : a = f
    · subst a
      simp [hfD, hfP, hfg]
    · simp [ha]
  have hspan : rowSpan (K := K) x ((ground H \ P) \ {g}) ≤ rowSpan x (ground H \ P) :=
    Submodule.span_mono (Set.image_mono Finset.sdiff_subset)
  have hm : IsMatching (ρ x) (insert T H) (insert T J) := by
    refine ⟨Finset.insert_subset_insert _ hJ,?_⟩
    rw [hu, rank_insert_of_outside x e _ (fun h => hsep (hspan h)), hind,
      Finset.card_insert_of_notMem hTJ]
    omega
  have hupper := matching_upper (K := K) x (H := insert T H) (J := insert T J)
    (fun A hA => (Finset.mem_insert.mp hA).elim (fun h => h ▸ hTD) (hp A))
    hm Z (augment_partition hπ hT)
  have hg : Z ∪ ground ({T} : Finset (Finset E)) = insert f Z := by
    rw [show ground ({T} : Finset (Finset E)) = T by simp [ground]]
    ext a
    simp only [T, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    by_cases h : a = e
    · subst a
      simp [heZ]
    · tauto
  have hr := rank_insert_le (K := K) x f Z
  unfold value at hupper ⊢
  rw [Finset.sum_insert hπT, hg, Finset.card_insert_of_notMem hTJ, hcardJ] at hupper
  omega

#print axioms outside_auxiliary

end
end Rigidity369952.Matching
```

## MatchingGlueRank.lean

```lean
import MatchingOutside
import GlueLiteral

open Set

set_option maxHeartbeats 260000

namespace Rigidity369952

noncomputable section
open Matching

def asFin {α : Type*} [Finite α] (s : Set α) : Finset α :=
  (Set.toFinite s).toFinset

@[simp] theorem coe_asFin {α : Type*} [Finite α] (s : Set α) :
    (asFin s : Set α) = s := Set.Finite.coe_toFinset _

@[simp] theorem mem_asFin {α : Type*} [Finite α] {s : Set α} {a : α} :
    a ∈ asFin s ↔ a ∈ s := Set.Finite.mem_toFinset _

theorem asFin_card {α : Type*} [Finite α] (s : Set α) : (asFin s).card = s.ncard := by
  rw [← Set.ncard_coe_finset, coe_asFin]

private theorem set_finset_nat_card {α : Type*} (A : Finset α) :
    Nat.card (A : Set α) = A.card := by
  let e : (A : Set α) ≃ ↥A :=
    ⟨fun a => ⟨a.1,a.2⟩, fun a => ⟨a.1,a.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

variable {d n : ℕ}
local notation "E" => Edge (Fin n)
local notation "F" => GenericField (Fin n) (Fin d)
local notation "x" => (genericRow (D := Fin d) : E → Fin n × Fin d → F)
def finGenericRank (d n : ℕ) (A : Finset (Edge (Fin n))) : ℕ :=
  genericRank (D := Fin d) (A : Set (Edge (Fin n)))

local notation "ρ" => (finGenericRank d n)

def gluedFamily (emb : GlueV d ↪ Fin n) (hodd : Odd d) : Finset (Finset E) := by
  classical
  exact Finset.univ.image (fun t => asFin (gluePair emb hodd t))

theorem mem_gluedFamily (emb : GlueV d ↪ Fin n) (hodd : Odd d) (P : Finset E) :
    P ∈ gluedFamily emb hodd ↔ ∃ t, asFin (gluePair emb hodd t) = P := by
  classical
  simp [gluedFamily]

theorem glued_two (emb : GlueV d ↪ Fin n) (hodd : Odd d) {P : Finset E}
    (hP : P ∈ gluedFamily emb hodd) : P.card = 2 := by
  obtain ⟨t,rfl⟩ := (mem_gluedFamily emb hodd P).mp hP
  rw [asFin_card, glue_pair_two]

theorem glued_disjoint (emb : GlueV d ↪ Fin n) (hodd : Odd d) :
    (gluedFamily emb hodd : Set (Finset E)).PairwiseDisjoint id := by
  intro P hP Q hQ hne
  obtain ⟨t,rfl⟩ := (mem_gluedFamily emb hodd P).mp hP
  obtain ⟨u,rfl⟩ := (mem_gluedFamily emb hodd Q).mp hQ
  have h := glue_pair_disjoint emb hodd (fun he : t = u => hne (congrArg (fun a => asFin (gluePair emb hodd a)) he))
  exact Finset.disjoint_left.mpr (fun _ ha hb => Set.disjoint_left.mp h (mem_asFin.mp ha) (mem_asFin.mp hb))

theorem glued_ground (emb : GlueV d ↪ Fin n) (hodd : Odd d) :
    (ground (gluedFamily emb hodd) : Set E) = glueGround emb := by
  classical
  rw [← glue_pairs_cover emb hodd]
  ext e
  constructor
  · intro he
    obtain ⟨P,hP,heP⟩ := Finset.mem_biUnion.mp he
    obtain ⟨t,rfl⟩ := (mem_gluedFamily emb hodd P).mp hP
    exact ⟨_,⟨t,rfl⟩,mem_asFin.mp heP⟩
  · rintro ⟨_,⟨t,rfl⟩,het⟩
    exact Finset.mem_biUnion.mpr ⟨_,(mem_gluedFamily emb hodd _).mpr ⟨t,rfl⟩,mem_asFin.mpr het⟩

theorem glued_ground_card (emb : GlueV d ↪ Fin n) (hodd : Odd d) :
    2 * (gluedFamily emb hodd).card = (d+3)*((d+2)^2+(d+2)-2) := by
  classical
  rw [← ground_card (fun P hP => glued_two emb hodd hP) (glued_disjoint emb hodd)]
  have he := Nat.card_congr (Equiv.ofInjective (glueEdge emb) (glueEdge_injective emb))
  change Nat.card (GlueIndex d) = Nat.card (glueGround emb) at he
  rw [← glued_ground emb hodd, set_finset_nat_card, Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_fin, glue_class_card] at he
  exact he.symm

theorem glued_rank (emb : GlueV d ↪ Fin n) (hd : 5 ≤ d) (hodd : Odd d) :
    ρ (ground (gluedFamily emb hodd)) = 2 * (gluedFamily emb hodd).card - 2 := by
  unfold finGenericRank
  rw [glued_ground, glue_ground_rank emb hd, glued_ground_card emb hodd]

theorem glued_erase_rank (emb : GlueV d ↪ Fin n) (hd : 5 ≤ d) (hodd : Odd d)
    {P : Finset E} (hP : P ∈ gluedFamily emb hodd) :
    ρ (ground ((gluedFamily emb hodd).erase P)) = 2 * (gluedFamily emb hodd).card - 3 := by
  obtain ⟨t,rfl⟩ := (mem_gluedFamily emb hodd P).mp hP
  rw [ground_erase (glued_disjoint emb hodd) hP]
  unfold finGenericRank
  rw [Finset.coe_sdiff, coe_asFin, glued_ground, glue_pair_deletion_rank emb hd hodd t,
    glued_ground_card emb hodd]

private theorem glued_subset_parameters (emb : GlueV d ↪ Fin n) (hodd : Odd d) (hd : 5 ≤ d)
    (A : Finset E) (hA : A ⊆ ground (gluedFamily emb hodd)) :
    ρ A + Module.finrank F (glueAllowedParameters emb (fun i => glueEdge emb i ∈ A)) = A.card := by
  classical
  let P (i : GlueIndex d) := glueEdge emb i ∈ A
  have he : glueSubset emb P = (A : Set E) := by
    ext e
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact hi
    · intro hem
      have hm := hA hem
      change e ∈ (ground (gluedFamily emb hodd) : Set E) at hm
      rw [glued_ground] at hm
      obtain ⟨i,rfl⟩ := hm
      exact ⟨i,hem,rfl⟩
  have hcard := Nat.card_congr (glueSubsetEquiv emb P)
  rw [he, set_finset_nat_card, Nat.card_eq_fintype_card] at hcard
  have h := glue_subset_rank_add emb hd P
  rw [he, hcard] at h
  change ρ A + _ = _ at h
  exact h

theorem glued_small_nullity (emb : GlueV d ↪ Fin n) (hodd : Odd d) (hd : 5 ≤ d)
    (A : Finset E) (hA : A ⊆ ground (gluedFamily emb hodd)) : A.card ≤ ρ A + 2 := by
  have h := glued_subset_parameters emb hodd hd A hA
  have hle := (glueAllowedParameters emb (fun i => glueEdge emb i ∈ A)).finrank_le
  rw [glue_parameter_dim emb] at hle
  omega

theorem glued_dependent_rank (emb : GlueV d ↪ Fin n) (hodd : Odd d) (hd : 5 ≤ d)
    (A : Finset E) (hA : A ⊆ ground (gluedFamily emb hodd)) (ha : ρ A < A.card) :
    (d+2)*((d+2)^2+(d+2)-2)-1 ≤ ρ A := by
  classical
  let P (i : GlueIndex d) := glueEdge emb i ∈ A
  have h : ρ A + Module.finrank F (glueAllowedParameters emb P) = A.card :=
    glued_subset_parameters emb hodd hd A hA
  have hoo : ∀ e f : GlueIndex d, ¬ P e → ¬ P f → e.1 = f.1 := by
    intro e f hE hF
    by_contra hne
    have hk := glue_allowed_cross emb P e f hE hF hne
    rw [hk, finrank_bot, add_zero] at h
    omega
  let j : GlueJ d := if he : ∃ e, ¬ P e then he.choose.1 else 0
  have hclass : ∀ i : GlueIndex d, i.1 ≠ j → P i := by
    intro i hi
    by_contra hn
    have hex : ∃ e, ¬ P e := ⟨i,hn⟩
    apply hi
    simpa only [j, dite_eq_left hex] using hoo i hex.choose hn hex.choose_spec
  have hsub : glueGround emb \ glueClassSet emb j ⊆ (A : Set E) := by
    rintro e ⟨⟨i,rfl⟩,hn⟩
    exact hclass i (fun hi => hn ⟨i,hi,rfl⟩)
  have hm : genericRank (D := Fin d) (glueGround emb \ glueClassSet emb j) ≤ ρ A :=
    Submodule.finrank_mono (Submodule.span_mono (Set.image_mono hsub))
  rwa [glue_class_complement_rank emb hd] at hm

theorem generic_edge_nonzero (hd : 0 < d) (e : E) : x e ≠ 0 := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hab : a ≠ b := fun h => he (by simp [h])
    intro hz
    let j : Fin d := ⟨0,hd⟩
    have hz' := congrFun hz (a,j)
    change orderedRow genericPosition a b (a,j) = 0 at hz'
    have hp : genericPosition (a,j) = genericPosition (b,j) := by
      apply sub_eq_zero.mp
      simpa [orderedRow,hab] using hz'
    exact hab (congrArg Prod.fst (MvPolynomial.X_injective
      (IsFractionRing.injective (Poly (Fin n) (Fin d)) F hp)))

#print axioms glued_rank
#print axioms glued_erase_rank
#print axioms glued_small_nullity
#print axioms glued_dependent_rank
#print axioms generic_edge_nonzero

end
end Rigidity369952
```

## MatchingGlueGap.lean

```lean
import MatchingGlueRank

open Set
open scoped BigOperators

set_option maxHeartbeats 300000

namespace Rigidity369952

noncomputable section
open Matching

variable {d n : ℕ}
local notation "E" => Edge (Fin n)
local notation "ρ" => (finGenericRank d n)

private theorem named_mem (emb : GlueV d ↪ Fin n) (hodd : Odd d) (t : GluePairName d) :
    asFin (gluePair emb hodd t) ∈ gluedFamily emb hodd :=
  (mem_gluedFamily emb hodd _).mpr ⟨t,rfl⟩

private theorem named_edge_mem (emb : GlueV d ↪ Fin n) (hodd : Odd d) (t : GluePairName d)
    (b : Fin 2) : glueEdge emb (gluePairIndex hodd t b) ∈ asFin (gluePair emb hodd t) :=
  mem_asFin.mpr ⟨b,rfl⟩

private theorem named_is_pair (emb : GlueV d ↪ Fin n) (hodd : Odd d) (t : GluePairName d) :
    asFin (gluePair emb hodd t) =
      {glueEdge emb (gluePairIndex hodd t 0), glueEdge emb (gluePairIndex hodd t 1)} := by
  classical
  ext e
  rw [mem_asFin]
  change (∃ b : Fin 2, glueEdge emb (gluePairIndex hodd t b) = e) ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨b,rfl⟩
    fin_cases b <;> simp
  · rintro (h | h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩

private theorem named_edges_ne (emb : GlueV d ↪ Fin n) (hodd : Odd d) (t : GluePairName d) :
    glueEdge emb (gluePairIndex hodd t 0) ≠ glueEdge emb (gluePairIndex hodd t 1) := by
  intro h
  have he : (t,(0 : Fin 2)) = (t,(1 : Fin 2)) :=
    (gluePairIndex_bijective hodd).1 (glueEdge_injective emb h)
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd he)

private theorem other_class (j : GlueJ d) : ∃ u : GluePairName d, j ≠ u.1 := by
  have h01 : (0 : GlueJ d) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  by_cases h : j = 0
  · exact ⟨(1,.inl 0),h ▸ h01⟩
  · exact ⟨(0,.inl 0),h⟩

private theorem named_ne (emb : GlueV d ↪ Fin n) (hodd : Odd d) {t u : GluePairName d}
    (h : t.1 ≠ u.1) : asFin (gluePair emb hodd t) ≠ asFin (gluePair emb hodd u) := by
  intro he
  have hx := named_edge_mem emb hodd t 0
  have hy := he ▸ hx
  have hd := glue_pair_disjoint emb hodd (fun htu => h (congrArg Prod.fst htu))
  exact Set.disjoint_left.mp hd (mem_asFin.mp hx) (mem_asFin.mp hy)

private theorem cross_deletion (emb : GlueV d ↪ Fin n) (hd : 5 ≤ d) (hodd : Odd d)
    (S : Finset E) (hS : S ⊆ ground (gluedFamily emb hodd)) (i j : GlueIndex d)
    (hi : glueEdge emb i ∈ S) (hj : glueEdge emb j ∈ S) (hij : i.1 ≠ j.1) :
    ρ (ground (gluedFamily emb hodd) \ S) = 2 * (gluedFamily emb hodd).card - S.card := by
  classical
  let T : Finset (GlueIndex d) := Finset.univ.filter (fun a => glueEdge emb a ∈ S)
  have he : T.image (glueEdge emb) = S := by
    ext e
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ha).2
    · intro h
      have hm := hS h
      change e ∈ (ground (gluedFamily emb hodd) : Set E) at hm
      rw [glued_ground] at hm
      obtain ⟨a,rfl⟩ := hm
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
  have ht := glue_delete_cross_rank emb hd T i j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩) hij
  rw [glue_delete_eq, ← Finset.coe_image, he, ← glued_ground emb hodd,
    ← Finset.coe_sdiff, ← glued_ground_card emb hodd] at ht
  have hcard : S.card = T.card := he ▸ Finset.card_image_of_injective T (glueEdge_injective emb)
  rw [hcard]
  exact ht

private theorem difference_union {α : Type*} [DecidableEq α] (D P Q : Finset α) :
    (D \ P) \ Q = D \ (P ∪ Q) := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

theorem glued_matching_max (emb : GlueV d ↪ Fin n) (hd : 5 ≤ d) (hodd : Odd d) :
    IsGreatest (MatchSizes ρ (gluedFamily emb hodd)) ((gluedFamily emb hodd).card - 2) := by
  classical
  let H := gluedFamily emb hodd
  let t : GluePairName d := (0,.inl 0)
  obtain ⟨u,htu⟩ := other_class t.1
  let P := asFin (gluePair emb hodd t)
  let Q := asFin (gluePair emb hodd u)
  have hP : P ∈ H := named_mem emb hodd t
  have hQ : Q ∈ H := named_mem emb hodd u
  have hne : P ≠ Q := named_ne emb hodd htu
  have hdPQ : Disjoint P Q := glued_disjoint emb hodd hP hQ hne
  have hcard : (P ∪ Q).card = 4 := by
    have h := Finset.card_union_add_card_inter P Q
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdPQ, Finset.card_empty,
      glued_two emb hodd hP, glued_two emb hodd hQ] at h
    omega
  have hQe : Q ∈ H.erase P := Finset.mem_erase.mpr ⟨Ne.symm hne,hQ⟩
  have hpos := Finset.card_pos.mpr ⟨Q,hQe⟩
  rw [Finset.card_erase_of_mem hP] at hpos
  have hEr : ((H.erase P).erase Q).card = H.card - 2 := by
    rw [Finset.card_erase_of_mem hQe, Finset.card_erase_of_mem hP]
    omega
  refine ⟨⟨(H.erase P).erase Q, ⟨fun _ h => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h), ?_⟩, hEr⟩, ?_⟩
  · have hS : P ∪ Q ⊆ ground H := by
      intro a ha
      exact (Finset.mem_union.mp ha).elim
        (fun hm => Finset.mem_biUnion.mpr ⟨P,hP,hm⟩) (fun hm => Finset.mem_biUnion.mpr ⟨Q,hQ,hm⟩)
    have hr := cross_deletion emb hd hodd (P ∪ Q) hS (gluePairIndex hodd t 0)
      (gluePairIndex hodd u 0) (Finset.mem_union_left _ (named_edge_mem emb hodd t 0))
      (Finset.mem_union_right _ (named_edge_mem emb hodd u 0)) htu
    change ρ (ground H \ (P ∪ Q)) = 2 * H.card - _ at hr
    rw [ground_erase_two (glued_disjoint emb hodd) hP hQ hne, difference_union, hr, hEr, hcard]
    omega
  · rintro a ⟨J,hJ,rfl⟩
    have hh : IsMatching ρ H J := hJ
    have hc := Finset.card_le_card hh.1
    by_cases he : J = H
    · subst J
      have hr := glued_rank emb hd hodd
      change ρ (ground H) = 2 * H.card - 2 at hr
      have hj := hh.2
      omega
    · obtain ⟨R,hR,hRJ⟩ : ∃ R ∈ H, R ∉ J := by
        by_contra! hn
        exact he (Finset.Subset.antisymm hh.1 hn)
      have hsub : J ⊆ H.erase R := fun A hA =>
        Finset.mem_erase.mpr ⟨fun he => hRJ (he ▸ hA),hh.1 hA⟩
      have hr : ρ (ground J) ≤ ρ (ground (H.erase R)) :=
        Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (ground_mono hsub)))
      rw [hh.2, glued_erase_rank emb hd hodd hR] at hr
      omega

theorem glued_outside_lower (d n : ℕ) (hd : 5 ≤ d) (hodd : Odd d)
    (hn : 2*(d+2)^2+2*(d+2)-1 ≤ n)
    (Z : Finset (Edge (Fin n))) {π : Finset (Finset (Finset (Edge (Fin n))))}
    (hπ : IsPartition (gluedFamily (glueEmbedding d n hn) hodd) π)
    (hZ : ¬ Z ⊆ ground (gluedFamily (glueEmbedding d n hn) hodd)) :
    (gluedFamily (glueEmbedding d n hn) hodd).card - 1 ≤
      value (finGenericRank d n) Z π := by
  classical
  let emb := glueEmbedding d n hn
  let H := gluedFamily emb hodd
  have hex : ∃ e ∈ Z, e ∉ ground H := by
    by_contra! h
    exact hZ h
  obtain ⟨e,heZ,heD⟩ := hex
  have heD' : e ∉ glueGround emb := by rw [← glued_ground emb hodd]; exact heD
  obtain ⟨P₀,⟨t,rfl⟩,hsep⟩ := glue_ambient_fin d n hd hodd hn e heD'
  obtain ⟨u,htu⟩ := other_class t.1
  let P := asFin (gluePair emb hodd t)
  let Q := asFin (gluePair emb hodd u)
  let f := glueEdge emb (gluePairIndex hodd u 0)
  let g := glueEdge emb (gluePairIndex hodd u 1)
  have hP : P ∈ H := named_mem emb hodd t
  have hQ : Q ∈ H := named_mem emb hodd u
  have hPQ : P ≠ Q := named_ne emb hodd htu
  have hgQ : g ∈ Q := named_edge_mem emb hodd u 1
  have hdis := glued_disjoint emb hodd hP hQ hPQ
  have hgP : g ∉ P := fun h => Finset.disjoint_left.mp hdis h hgQ
  have hS : P ∪ {g} ⊆ ground H := by
    intro a ha
    rcases Finset.mem_union.mp ha with hp | hg
    · exact Finset.mem_biUnion.mpr ⟨P,hP,hp⟩
    · exact Finset.mem_biUnion.mpr ⟨Q,hQ,(Finset.mem_singleton.mp hg).symm ▸ hgQ⟩
  have hr := cross_deletion emb hd hodd (P ∪ {g}) hS (gluePairIndex hodd t 0)
    (gluePairIndex hodd u 1) (Finset.mem_union_left _ (named_edge_mem emb hodd t 0))
    (Finset.mem_union_right _ (Finset.mem_singleton_self g)) htu
  have hc : (P ∪ {g}).card = 3 := by
    rw [Finset.union_comm, Finset.singleton_union, Finset.card_insert_of_notMem hgP, glued_two emb hodd hP]
  rw [← difference_union, hc] at hr
  have hsp : genericRow (D := Fin d) e ∉ rowSpan
      (K := GenericField (Fin n) (Fin d)) (genericRow (D := Fin d)) (ground H \ P) := by
    unfold rowSpan
    rw [Finset.coe_sdiff, glued_ground, coe_asFin]
    exact hsep
  exact outside_auxiliary (K := GenericField (Fin n) (Fin d)) (genericRow (D := Fin d))
    (fun A hA => glued_two emb hodd hA) (glued_disjoint emb hodd)
    hπ heZ heD hP hQ hPQ (named_is_pair emb hodd u) (named_edges_ne emb hodd u) hr hsp

#print axioms glued_matching_max
#print axioms glued_outside_lower

end
end Rigidity369952
```

## MatchingEndpoint.lean

```lean
import MatchingGlueGap

open Set
open scoped BigOperators

namespace Rigidity369952

noncomputable section
open Matching

def matchingThreshold (d : ℕ) : ℕ := 2*(d+2)^2+2*(d+2)-1

def genericCompleteRank (d n : ℕ) (A : Finset (Edge (Fin n))) : ℕ :=
  genericRank (D := Fin d) (A : Set (Edge (Fin n)))

def realCompleteRank {d n : ℕ} (p : Fin n × Fin d → ℝ) (A : Finset (Edge (Fin n))) : ℕ :=
  realRowRank p (A : Set (Edge (Fin n)))

theorem realCompleteRank_eq {d n : ℕ} (p : Fin n × Fin d → ℝ)
    (hp : AlgebraicIndependent ℚ p) : realCompleteRank p = genericCompleteRank d n := by
  funext A
  exact real_rank_eq_genericRank p hp _

private theorem empty_flat {d n : ℕ} (hd : 0 < d) :
    IsFlat (genericCompleteRank d n) ∅ := by
  let K := GenericField (Fin n) (Fin d)
  let x := (genericRow (D := Fin d) : Edge (Fin n) → Fin n × Fin d → K)
  change IsFlat (rowRank (K := K) x) ∅
  intro e
  have hspan : rowSpan (K := K) x ∅ = ⊥ := by
    unfold rowSpan
    have he : x '' ((∅ : Finset (Edge (Fin n))) : Set (Edge (Fin n))) = ∅ := by ext a; simp
    rw [he, Submodule.span_empty]
  have hout : x e ∉ rowSpan (K := K) x ∅ := by
    rw [hspan, Submodule.mem_bot]
    exact generic_edge_nonzero hd e
  rw [rank_insert_of_outside x e ∅ hout]
  simp

theorem glued_cover_min (d n : ℕ) (hd : 5 ≤ d) (hodd : Odd d)
    (hn : matchingThreshold d ≤ n) :
    let H := gluedFamily (glueEmbedding d n hn) hodd
    IsLeast (CoverValues (genericCompleteRank d n) H) (H.card - 1) := by
  classical
  dsimp only
  let emb := glueEmbedding d n hn
  let H := gluedFamily emb hodd
  let L := (d+2)^2+(d+2)-2
  let C := (d+2)*L
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hC' : 2*L ≤ C := Nat.mul_le_mul_right L (by omega)
  have hH := glued_ground_card emb hodd
  change 2 * H.card = (d+3)*L at hH
  have hb : (d+3)*L = C + L := by
    change ((d+2)+1)*L = (d+2)*L + L
    rw [Nat.add_mul, one_mul]
  rw [hb] at hH
  have hC : H.card + 1 ≤ C := by omega
  have hpos : 0 < H.card := by omega
  change IsLeast (CoverValues (genericCompleteRank d n) H) (H.card - 1)
  refine ⟨⟨∅,{H},empty_flat (by omega),?_,?_⟩,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro B hB
      obtain rfl := Finset.mem_singleton.mp hB
      exact Finset.card_pos.mp hpos
    · intro B hB A hA hne
      change B ∈ ({H} : Finset _) at hB
      change A ∈ ({H} : Finset _) at hA
      exact (hne ((Finset.mem_singleton.mp hB).trans (Finset.mem_singleton.mp hA).symm)).elim
    · simp
  · have hr := glued_rank emb hd hodd
    change genericCompleteRank d n (ground H) = 2*H.card-2 at hr
    have hzero : genericCompleteRank d n ∅ = 0 :=
      rank_empty (K := GenericField (Fin n) (Fin d)) _
    unfold value
    rw [Finset.sum_singleton, hzero, Finset.empty_union, hr]
    omega
  · rintro a ⟨Z,π,_,hπ,rfl⟩
    by_cases hZ : Z ⊆ ground H
    · exact inside_lower _ (fun P hP => glued_two emb hodd hP) (glued_disjoint emb hodd)
        hπ Z hZ C hC
        (fun A _ => rank_card (K := GenericField (Fin n) (Fin d)) (genericRow (D := Fin d)) A)
        (glued_small_nullity emb hodd hd)
        (glued_dependent_rank emb hodd hd)
    · exact glued_outside_lower d n hd hodd hn Z hπ hZ

theorem glued_exact_generic (d n : ℕ) (hd : 5 ≤ d) (hodd : Odd d)
    (hn : matchingThreshold d ≤ n) :
    let H := gluedFamily (glueEmbedding d n hn) hodd
    IsGreatest (MatchSizes (genericCompleteRank d n) H) (H.card - 2) ∧
    IsLeast (CoverValues (genericCompleteRank d n) H) (H.card - 1) :=
  ⟨glued_matching_max (glueEmbedding d n hn) hd hodd, glued_cover_min d n hd hodd hn⟩

theorem glued_exact_real (d n : ℕ) (hd : 5 ≤ d) (hodd : Odd d)
    (hn : matchingThreshold d ≤ n) (p : Fin n × Fin d → ℝ) (hp : AlgebraicIndependent ℚ p) :
    let H := gluedFamily (glueEmbedding d n hn) hodd
    IsGreatest (MatchSizes (realCompleteRank p) H) (H.card - 2) ∧
    IsLeast (CoverValues (realCompleteRank p) H) (H.card - 1) := by
  rw [realCompleteRank_eq p hp]
  exact glued_exact_generic d n hd hodd hn

theorem odd_complete_matching_failure (k n : ℕ) (hk : 2 ≤ k)
    (hn : matchingThreshold (2*k+1) ≤ n) :
    ¬ HasMatchingProperty (genericCompleteRank (2*k+1) n) := by
  let d := 2*k+1
  have hd : 5 ≤ d := by dsimp [d]; omega
  have hodd : Odd d := ⟨k,rfl⟩
  let H := gluedFamily (glueEmbedding d n hn) hodd
  obtain ⟨hmax,hmin⟩ := glued_exact_generic d n hd hodd hn
  have hh := glued_ground_card (glueEmbedding d n hn) hodd
  have hm : 4 ≤ 2 * H.card := by
    change 2 * H.card = _ at hh
    rw [hh]
    exact Nat.mul_le_mul (show 2 ≤ d+3 by omega) (show 2 ≤ (d+2)^2+(d+2)-2 by omega)
  intro hprop
  obtain ⟨a,ha,hb⟩ := hprop H (fun P hP => glued_two (glueEmbedding d n hn) hodd hP)
  have he := ha.unique hmax
  have he' := hb.unique hmin
  change a = H.card - 2 at he
  change a = H.card - 1 at he'
  omega

theorem mathdb369952_generic :
    ∀ k : ℕ, 2 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ HasMatchingProperty (genericCompleteRank (2*k+1) n) :=
  fun k hk => ⟨matchingThreshold (2*k+1), fun n hn => odd_complete_matching_failure k n hk hn⟩

theorem mathdb369952_real :
    ∀ k : ℕ, 2 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∃ p : Fin n × Fin (2*k+1) → ℝ, AlgebraicIndependent ℚ p) ∧
      ∀ p : Fin n × Fin (2*k+1) → ℝ, AlgebraicIndependent ℚ p →
        ¬ HasMatchingProperty (realCompleteRank p) := by
  intro k hk
  refine ⟨matchingThreshold (2*k+1),fun n hn => ⟨real_algebraicIndependent_exists _,?_⟩⟩
  intro p hp
  rw [realCompleteRank_eq p hp]
  exact odd_complete_matching_failure k n hk hn

#print axioms realCompleteRank_eq
#print axioms glued_cover_min
#print axioms glued_exact_generic
#print axioms glued_exact_real
#print axioms odd_complete_matching_failure
#print axioms mathdb369952_generic
#print axioms mathdb369952_real

end
end Rigidity369952
```

## MatchingNativeSets.lean

```lean
import MatchingEndpoint

open scoped BigOperators

namespace Rigidity369952.Matching

noncomputable section
namespace Native

variable {E : Type*} [Finite E] [DecidableEq E]

def toFin {α β : Type*} [Finite α] (e : α ≃ β) : Set α ≃ Finset β where
  toFun S := (asFin S).map e.toEmbedding
  invFun F := e ⁻¹' (F : Set β)
  left_inv S := by
    ext a
    change e a ∈ (asFin S).map e.toEmbedding ↔ a ∈ S
    rw [Finset.mem_map_equiv, e.symm_apply_apply, mem_asFin]
  right_inv F := by
    ext b
    change b ∈ (asFin (e ⁻¹' (F : Set β))).map e.toEmbedding ↔ b ∈ F
    rw [Finset.mem_map_equiv, mem_asFin]
    change e (e.symm b) ∈ F ↔ b ∈ F
    rw [e.apply_symm_apply]

def edges : Set E ≃ Finset E := toFin (Equiv.refl E)

def family : Set (Set E) ≃ Finset (Finset E) := toFin edges

def partition : Set (Set (Set E)) ≃ Finset (Finset (Finset E)) := toFin family

@[simp] theorem mem_toFin {α β : Type*} [Finite α] (e : α ≃ β) (S : Set α) (a : α) :
    e a ∈ toFin e S ↔ a ∈ S := by
  change e a ∈ (asFin S).map e.toEmbedding ↔ _
  rw [Finset.mem_map_equiv, e.symm_apply_apply, mem_asFin]

omit [DecidableEq E] in
@[simp] theorem mem_edges {Z : Set E} {e : E} : e ∈ edges Z ↔ e ∈ Z :=
  mem_toFin (Equiv.refl E) Z e

omit [DecidableEq E] in
@[simp] theorem mem_family {H : Set (Set E)} {P : Set E} : edges P ∈ family H ↔ P ∈ H :=
  mem_toFin edges H P

omit [DecidableEq E] in
@[simp] theorem mem_partition {π : Set (Set (Set E))} {B : Set (Set E)} :
    family B ∈ partition π ↔ B ∈ π :=
  mem_toFin family π B

omit [DecidableEq E] in
@[simp] theorem coe_edges (Z : Set E) : (edges Z : Set E) = Z := by
  ext e
  exact mem_edges

omit [DecidableEq E] in
@[simp] theorem edges_card (Z : Set E) : (edges Z).card = Z.ncard := by
  rw [← Set.ncard_coe_finset, coe_edges]

omit [DecidableEq E] in
@[simp] theorem family_card (H : Set (Set E)) : (family H).card = H.ncard := by
  change ((asFin H).map edges.toEmbedding).card = _
  rw [Finset.card_map, asFin_card]

theorem ground_family (H : Set (Set E)) : (ground (family H) : Set E) = ⋃₀ H := by
  ext e
  change e ∈ ground (family H) ↔ _
  constructor
  · intro h
    obtain ⟨P,hP,he⟩ := Finset.mem_biUnion.mp h
    obtain ⟨A,rfl⟩ := edges.surjective P
    exact ⟨A,mem_family.mp hP,mem_edges.mp he⟩
  · rintro ⟨A,hA,he⟩
    exact Finset.mem_biUnion.mpr ⟨edges A,mem_family.mpr hA,mem_edges.mpr he⟩

def IsPartition (H : Set (Set E)) (π : Set (Set (Set E))) : Prop :=
  (∀ B ∈ π, B.Nonempty) ∧ π.PairwiseDisjoint id ∧ ⋃₀ π = H

theorem partition_iff (H : Set (Set E)) (π : Set (Set (Set E))) :
    Matching.IsPartition (family H) (partition π) ↔ IsPartition H π := by
  have hne (A : Set (Set E)) : (family A).Nonempty ↔ A.Nonempty := by
    constructor
    · rintro ⟨P,hP⟩
      obtain ⟨Q,rfl⟩ := edges.surjective P
      exact ⟨Q,mem_family.mp hP⟩
    · rintro ⟨P,hP⟩
      exact ⟨edges P,mem_family.mpr hP⟩
  have hdis (A B : Set (Set E)) : Disjoint (family A) (family B) ↔ Disjoint A B := by
    constructor
    · intro h
      exact Set.disjoint_left.mpr (fun P ha hb =>
        Finset.disjoint_left.mp h (mem_family.mpr ha : edges P ∈ family A) (mem_family.mpr hb))
    · intro h
      apply Finset.disjoint_left.mpr
      intro P ha hb
      obtain ⟨Q,rfl⟩ := edges.surjective P
      exact Set.disjoint_left.mp h (mem_family.mp ha) (mem_family.mp hb)
  have hcov : (partition π).biUnion id = family (⋃₀ π) := by
    ext P
    obtain ⟨Q,rfl⟩ := edges.surjective P
    rw [mem_family]
    constructor
    · intro h
      obtain ⟨B,hB,hQ⟩ := Finset.mem_biUnion.mp h
      obtain ⟨A,rfl⟩ := family.surjective B
      exact ⟨A,mem_partition.mp hB,mem_family.mp hQ⟩
    · rintro ⟨A,hA,hQ⟩
      exact Finset.mem_biUnion.mpr ⟨family A,mem_partition.mpr hA,mem_family.mpr hQ⟩
  unfold Matching.IsPartition IsPartition
  rw [hcov]
  constructor
  · rintro ⟨hn,hd,hc⟩
    exact ⟨fun B hB => (hne B).mp (hn _ (mem_partition.mpr hB)),
      fun A hA B hB hab => (hdis A B).mp (hd (mem_partition.mpr hA) (mem_partition.mpr hB)
        (fun h => hab (family.injective h))), family.injective hc⟩
  · rintro ⟨hn,hd,rfl⟩
    refine ⟨?_,?_,rfl⟩
    · intro B hB
      obtain ⟨A,rfl⟩ := family.surjective B
      exact (hne A).mpr (hn A (mem_partition.mp hB))
    · intro A hA B hB hab
      obtain ⟨X,rfl⟩ := family.surjective A
      obtain ⟨Y,rfl⟩ := family.surjective B
      exact (hdis X Y).mpr (hd (mem_partition.mp hA) (mem_partition.mp hB)
        (fun h => hab (congrArg family h)))

def IsFlat (r : Set E → ℕ) (Z : Set E) : Prop :=
  ∀ e, r (insert e Z) = r Z ↔ e ∈ Z

def IsMatching (r : Set E → ℕ) (H J : Set (Set E)) : Prop :=
  J ⊆ H ∧ r (⋃₀ J) = 2*J.ncard

def value (r : Set E → ℕ) (Z : Set E) (π : Set (Set (Set E))) : ℕ :=
  r Z + ∑ B ∈ asFin π, (r (Z ∪ ⋃₀ B) - r Z) / 2

def MatchSizes (r : Set E → ℕ) (H : Set (Set E)) : Set ℕ :=
  {v | ∃ J, IsMatching r H J ∧ J.ncard = v}

def CoverValues (r : Set E → ℕ) (H : Set (Set E)) : Set ℕ :=
  {v | ∃ Z π, IsFlat r Z ∧ IsPartition H π ∧ value r Z π = v}

def HasMatchingProperty (r : Set E → ℕ) : Prop :=
  ∀ H : Set (Set E), (∀ P ∈ H, P.ncard = 2) →
    ∃ a, IsGreatest (MatchSizes r H) a ∧ IsLeast (CoverValues r H) a

variable (r : Set E → ℕ)
local notation "rF" => (fun A : Finset E => r (A : Set E))

theorem flat_iff (Z : Set E) : Matching.IsFlat rF (edges Z) ↔ IsFlat r Z := by
  unfold Matching.IsFlat IsFlat
  simp only [Finset.coe_insert, coe_edges, mem_edges]

theorem matching_iff (H J : Set (Set E)) :
    Matching.IsMatching rF (family H) (family J) ↔ IsMatching r H J := by
  unfold Matching.IsMatching IsMatching
  dsimp only
  rw [ground_family, family_card]
  have h : family J ⊆ family H ↔ J ⊆ H := by
    constructor
    · intro hf P hP
      exact mem_family.mp (hf (mem_family.mpr hP))
    · intro hs P hP
      obtain ⟨A,rfl⟩ := edges.surjective P
      exact mem_family.mpr (hs (mem_family.mp hP))
  rw [h]

theorem value_eq (Z : Set E) (π : Set (Set (Set E))) :
    Matching.value rF (edges Z) (partition π) = value r Z π := by
  unfold Matching.value value
  dsimp only
  rw [coe_edges]
  change r Z + ∑ B ∈ (asFin π).map family.toEmbedding,
    (r ((↑(edges Z ∪ ground B)) : Set E) - r Z) / 2 = _
  rw [Finset.sum_map]
  simp only [Equiv.toEmbedding_apply, Finset.coe_union, coe_edges, ground_family]

theorem matchSizes_eq (H : Set (Set E)) :
    Matching.MatchSizes rF (family H) = MatchSizes r H := by
  ext a
  constructor
  · rintro ⟨J,hj,ha⟩
    obtain ⟨A,rfl⟩ := family.surjective J
    exact ⟨A,(matching_iff r H A).mp hj,(family_card A).symm.trans ha⟩
  · rintro ⟨J,hj,ha⟩
    exact ⟨family J,(matching_iff r H J).mpr hj,(family_card J).trans ha⟩

theorem coverValues_eq (H : Set (Set E)) :
    Matching.CoverValues rF (family H) = CoverValues r H := by
  ext a
  constructor
  · rintro ⟨Z,π,hz,hπ,ha⟩
    obtain ⟨A,rfl⟩ := edges.surjective Z
    obtain ⟨B,rfl⟩ := partition.surjective π
    exact ⟨A,B,(flat_iff r A).mp hz,(partition_iff H B).mp hπ,(value_eq r A B).symm.trans ha⟩
  · rintro ⟨Z,π,hz,hπ,ha⟩
    exact ⟨edges Z,partition π,(flat_iff r Z).mpr hz,(partition_iff H π).mpr hπ,(value_eq r Z π).trans ha⟩

theorem property_iff : Matching.HasMatchingProperty rF ↔ HasMatchingProperty r := by
  constructor
  · intro h H hp
    have h₂ (P : Finset E) (hP : P ∈ family H) : P.card = 2 := by
      obtain ⟨A,rfl⟩ := edges.surjective P
      rw [edges_card]
      exact hp _ (mem_family.mp hP)
    simpa only [matchSizes_eq, coverValues_eq] using h (family H) h₂
  · intro h H hp
    obtain ⟨A,rfl⟩ := family.surjective H
    have h₂ (P : Set E) (hP : P ∈ A) : P.ncard = 2 := by
      rw [← edges_card]
      exact hp _ (mem_family.mpr hP)
    simpa only [matchSizes_eq, coverValues_eq] using h A h₂

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem representable_upper (x : E → V) (H J : Set (Set E))
    (hp : ∀ P ∈ H, P.ncard = 2)
    (hJ : IsMatching (fun A => Module.finrank K (Submodule.span K (x '' A))) H J)
    (Z : Set E) (π : Set (Set (Set E))) (hπ : IsPartition H π) :
    J.ncard ≤ value (fun A => Module.finrank K (Submodule.span K (x '' A))) Z π := by
  let r := fun A : Set E => Module.finrank K (Submodule.span K (x '' A))
  have h₂ (P : Finset E) (hP : P ∈ family H) : P.card = 2 := by
    obtain ⟨A,rfl⟩ := edges.surjective P
    rw [edges_card]
    exact hp _ (mem_family.mp hP)
  have h := matching_upper (K := K) x h₂ ((matching_iff r H J).mpr hJ)
    (edges Z) ((partition_iff H π).mpr hπ)
  change (family J).card ≤ Matching.value (fun A : Finset E => r (A : Set E)) (edges Z) (partition π) at h
  rwa [family_card, value_eq r Z π] at h

#print axioms partition_iff
#print axioms property_iff
#print axioms representable_upper

end Native
end
end Rigidity369952.Matching
```

## MatchingLiteral.lean

```lean
import MatchingNativeSets

namespace Rigidity369952

noncomputable section
open Matching

private theorem encode_gluedFamily {d n : ℕ} (emb : GlueV d ↪ Fin n) (hodd : Odd d) :
    Native.family (gluePairFamily emb hodd) = gluedFamily emb hodd := by
  ext P
  obtain ⟨A,rfl⟩ := Native.edges.surjective P
  rw [Native.mem_family, mem_gluedFamily]
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t, Finset.coe_injective (by rw [coe_asFin, Native.coe_edges])⟩
  · rintro ⟨t,ht⟩
    refine ⟨t,?_⟩
    simpa only [coe_asFin, Native.coe_edges] using
      (congrArg (fun Q : Finset (Edge (Fin n)) => (Q : Set (Edge (Fin n)))) ht)

theorem actual_glued_generic_extrema (d n : ℕ) (hd : 5 ≤ d) (hodd : Odd d)
    (hn : 2*(d+2)^2+2*(d+2)-1 ≤ n) :
    let H := gluePairFamily (glueEmbedding d n hn) hodd
    IsGreatest (Native.MatchSizes (genericRank (D := Fin d)) H) (H.ncard - 2) ∧
    IsLeast (Native.CoverValues (genericRank (D := Fin d)) H) (H.ncard - 1) := by
  dsimp only
  let H := gluePairFamily (glueEmbedding d n hn) hodd
  change IsGreatest (Native.MatchSizes (genericRank (D := Fin d)) H) (H.ncard - 2) ∧
    IsLeast (Native.CoverValues (genericRank (D := Fin d)) H) (H.ncard - 1)
  rw [← Native.matchSizes_eq, ← Native.coverValues_eq, ← Native.family_card H, encode_gluedFamily]
  exact glued_exact_generic d n hd hodd hn

theorem actual_glued_real_extrema (d n : ℕ) (hd : 5 ≤ d) (hodd : Odd d)
    (hn : 2*(d+2)^2+2*(d+2)-1 ≤ n) (p : Fin n × Fin d → ℝ) (hp : AlgebraicIndependent ℚ p) :
    let H := gluePairFamily (glueEmbedding d n hn) hodd
    IsGreatest (Native.MatchSizes (realRowRank p) H) (H.ncard - 2) ∧
    IsLeast (Native.CoverValues (realRowRank p) H) (H.ncard - 1) := by
  have hr : realRowRank p = genericRank (D := Fin d) := funext (real_rank_eq_genericRank p hp)
  rw [hr]
  exact actual_glued_generic_extrema d n hd hodd hn

theorem literal_matching_failure_at_threshold (k n : ℕ) (hk : 2 ≤ k)
    (hn : 2*((2*k+1)+2)^2+2*((2*k+1)+2)-1 ≤ n) :
    ¬ Native.HasMatchingProperty
      (genericRank (V := Fin n) (D := Fin (2*k+1))) := by
  intro h
  exact odd_complete_matching_failure k n hk hn ((Native.property_iff _).mpr h)

theorem literal_mathdb369952_arxiv_v1_v2 :
    ∀ k : ℕ, 2 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ Native.HasMatchingProperty (genericRank (V := Fin n) (D := Fin (2*k+1))) :=
  fun k hk => ⟨2*((2*k+1)+2)^2+2*((2*k+1)+2)-1,
    fun n hn => literal_matching_failure_at_threshold k n hk hn⟩

theorem literal_mathdb369952_all_independent_real :
    ∀ k : ℕ, 2 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∃ p : Fin n × Fin (2*k+1) → ℝ, AlgebraicIndependent ℚ p) ∧
      ∀ p : Fin n × Fin (2*k+1) → ℝ, AlgebraicIndependent ℚ p →
        ¬ Native.HasMatchingProperty (realRowRank p) := by
  intro k hk
  refine ⟨2*((2*k+1)+2)^2+2*((2*k+1)+2)-1,
    fun n hn => ⟨real_algebraicIndependent_exists _,?_⟩⟩
  intro p hp
  have hr : realRowRank p = genericRank (D := Fin (2*k+1)) :=
    funext (real_rank_eq_genericRank p hp)
  rw [hr]
  exact literal_matching_failure_at_threshold k n hk hn

#check Native.representable_upper
#check Native.partition_iff
#check actual_glued_generic_extrema
#check actual_glued_real_extrema
#check literal_matching_failure_at_threshold
#check literal_mathdb369952_arxiv_v1_v2
#check literal_mathdb369952_all_independent_real

#print axioms actual_glued_generic_extrema
#print axioms actual_glued_real_extrema
#print axioms literal_matching_failure_at_threshold
#print axioms literal_mathdb369952_arxiv_v1_v2
#print axioms literal_mathdb369952_all_independent_real

end
end Rigidity369952
```

## MatchingAudit.lean

```lean
import MatchingLiteral
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

namespace Rigidity369952.Matching

noncomputable section

variable {E K V : Type*} [DecidableEq E] [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]

local notation "ρ" => rowRank (K := K)

omit [DecidableEq E] [Module.Finite K V] in
theorem rank_card_iff_independent (x : E → V) (A : Finset E) :
    ρ x A = A.card ↔ LinearIndependent K (fun a : ↥A => x a.1) := by
  have hr : Set.range (fun a : ↥A => x a.1) = x '' (A : Set E) := by
    ext y
    exact ⟨fun ⟨a,ha⟩ => ⟨a.1,a.2,ha⟩,fun ⟨a,ha,hy⟩ => ⟨⟨a,ha⟩,hy⟩⟩
  rw [linearIndependent_iff_card_eq_finrank_span, hr, Fintype.card_coe]
  exact ⟨Eq.symm,Eq.symm⟩

omit [Module.Finite K V] in
theorem matching_rows_independent (x : E → V) {H J : Finset (Finset E)}
    (hp : ∀ P ∈ H, P.card = 2) (hj : IsMatching (ρ x) H J) :
    LinearIndependent K (fun a : ↥(ground J) => x a.1) := by
  apply (rank_card_iff_independent x _).mp
  rw [ground_card (fun P hP => hp P (hj.1 hP)) (selected_disjoint x hp hj)]
  exact hj.2

theorem flat_iff_row_closure (x : E → V) (Z : Finset E) :
    IsFlat (ρ x) Z ↔ ∀ e, x e ∈ rowSpan (K := K) x Z ↔ e ∈ Z := by
  have heq (e : E) : ρ x (insert e Z) = ρ x Z ↔ x e ∈ rowSpan (K := K) x Z := by
    constructor
    · intro hr
      by_contra hm
      have ht := rank_insert_of_outside (K := K) x e Z hm
      omega
    · intro he
      have hs : rowSpan (K := K) x (insert e Z) = rowSpan x Z := by
        apply le_antisymm
        · apply Submodule.span_le.mpr
          rintro _ ⟨a,ha,rfl⟩
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact he
          · exact Submodule.subset_span ⟨a,ha,rfl⟩
        · exact Submodule.span_mono (Set.image_mono (Finset.subset_insert e Z))
      exact congrArg (fun S : Submodule K V => Module.finrank K S) hs
  unfold IsFlat
  simp only [heq]

#check rowSpan
#check rowRank
#check IsFlat
#check IsPartition
#check IsMatching
#check value
#check rank_submod
#check selected_disjoint
#check rank_card_iff_independent
#check matching_rows_independent
#check flat_iff_row_closure
#check matching_upper
#check inside_lower
#check outside_auxiliary
#check glued_ground
#check glued_ground_card
#check glued_rank
#check glued_erase_rank
#check glued_small_nullity
#check glued_dependent_rank
#check generic_edge_nonzero
#check glued_matching_max
#check glued_outside_lower
#check glued_cover_min
#check real_rank_eq_genericRank
#check real_placement_with_all_generic_ranks
#check Native.IsFlat
#check Native.IsPartition
#check Native.IsMatching
#check Native.value
#check Native.HasMatchingProperty
#check Native.partition_iff
#check Native.matchSizes_eq
#check Native.coverValues_eq
#check Native.property_iff

#print axioms rank_card_iff_independent
#print axioms matching_rows_independent
#print axioms flat_iff_row_closure

end
end Rigidity369952.Matching
```

