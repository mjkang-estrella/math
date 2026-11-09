import ASEPMain

set_option linter.unusedSimpArgs false

/-!
# Transfer to the literal arc space `ℝ^A`, `A = {(i,j) : i ≠ j}`

The source defines `P_ASEP^n := {x ∈ ℝ^m | (2)–(4), x ≥ 0}` with coordinates indexed by the
`m = n(n-1)` arcs.  Here we state the polytope, vertices, tours and adjacency literally on arc-indexed
vectors and transfer the counterexample through the zero-diagonal embedding.
-/

namespace ASEP

open Finset

/-- Arcs of the complete digraph on `Fin n`. -/
abbrev Arc (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- `P_ASEP^n` on arc coordinates: source (2), (3), (4) with `δ(S) = {(i,j) : i ∈ S, j ∉ S}`, and `x ≥ 0`. -/
def arcPolytope (n : ℕ) : Set (Arc n → ℝ) :=
  {y | (∀ a, 0 ≤ y a) ∧ (∀ j : Fin n, ∑ a ∈ univ.filter (fun a : Arc n => a.1.2 = j), y a = 1) ∧
    (∀ i : Fin n, ∑ a ∈ univ.filter (fun a : Arc n => a.1.1 = i), y a = 1) ∧
    ∀ S : Finset (Fin n), 2 ≤ S.card → S.card ≤ n - 2 →
      1 ≤ ∑ a ∈ univ.filter (fun a : Arc n => a.1.1 ∈ S ∧ a.1.2 ∉ S), y a}

/-- Incidence vector of the tour with successor map `σ`. -/
def arcTour {n : ℕ} (σ : Equiv.Perm (Fin n)) : Arc n → ℝ := fun a => if σ a.1.1 = a.1.2 then 1 else 0

def IsArcTour (n : ℕ) (t : Arc n → ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), σ.IsCycle ∧ σ.support = Finset.univ ∧ t = arcTour σ

def ArcAdjacent (n : ℕ) (x y : Arc n → ℝ) : Prop :=
  x ∈ Set.extremePoints ℝ (arcPolytope n) ∧ y ∈ Set.extremePoints ℝ (arcPolytope n) ∧ x ≠ y ∧
    IsExtreme ℝ (arcPolytope n) (segment ℝ x y)

/-- Conjecture 1 stated on `ℝ^A`. -/
def ArcNeighborhoodTourConjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ x ∈ Set.extremePoints ℝ (arcPolytope n), ∃ t, IsArcTour n t ∧ ArcAdjacent n x t

/-- Zero-diagonal embedding into matrices. -/
def emb {n : ℕ} (y : Arc n → ℝ) : Fin n → Fin n → ℝ := fun i j => if h : i ≠ j then y ⟨(i, j), h⟩ else 0

/-- Restriction of a matrix to the arcs. -/
def res {n : ℕ} (x : Fin n → Fin n → ℝ) : Arc n → ℝ := fun a => x a.1.1 a.1.2

lemma res_emb {n : ℕ} (y : Arc n → ℝ) : res (emb y) = y := by
  funext a; simp [res, emb, a.2]

lemma emb_res {n : ℕ} (x : Fin n → Fin n → ℝ) (hx : ∀ i, x i i = 0) : emb (res x) = x := by
  funext i j; by_cases h : i = j
  · subst h; simp [emb, hx]
  · simp [emb, res, h]

lemma emb_add {n : ℕ} (y w : Arc n → ℝ) : emb (y + w) = emb y + emb w := by
  funext i j; by_cases h : i = j <;> simp [emb, h]

lemma emb_smul {n : ℕ} (c : ℝ) (y : Arc n → ℝ) : emb (c • y) = c • emb y := by
  funext i j; by_cases h : i = j <;> simp [emb, h]

lemma emb_injective {n : ℕ} : Function.Injective (emb (n := n)) := fun y w h => by
  rw [← res_emb y, ← res_emb w, h]

lemma flux_ite_expand_general {n : ℕ} (x : Fin n → Fin n → ℝ) (S : Finset (Fin n)) :
    flux x S = ∑ i, ∑ j, if (i ∈ S ∧ j ∉ S) then x i j else 0 := by
  unfold flux
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S)]
  have h1 : Finset.univ.filter (fun i => i ∈ S) = S := by ext; simp
  rw [h1]
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ i ∈ S), ∑ j, (if (i ∈ S ∧ j ∉ S) then x i j else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i hi; simp only [Finset.mem_filter] at hi; simp [hi.2]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← Finset.sum_filter]; congr 1; ext j; simp [hi]

/-- Filtered arc sums are double sums of the embedded matrix. -/
lemma arc_sum {n : ℕ} (y : Arc n → ℝ) (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)] :
    ∑ a ∈ univ.filter (fun a : Arc n => P a.1.1 a.1.2), y a =
      ∑ i, ∑ j, if P i j then emb y i j else 0 := by
  have hg : ∀ p : Fin n × Fin n, ¬ (p.1 ≠ p.2) → (if P p.1 p.2 then emb y p.1 p.2 else 0) = 0 := by
    intro p hp; simp only [ne_eq, not_not] at hp; simp [emb, hp]
  rw [← Finset.sum_product' (f := fun i j => if P i j then emb y i j else 0), Finset.univ_product_univ]
  rw [← Finset.sum_filter_of_ne (p := fun p : Fin n × Fin n => p.1 ≠ p.2)
    (fun p _ h => by by_contra hc; exact h (hg p (by simpa using hc)))]
  rw [Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2) (p := fun p : Fin n × Fin n => p.1 ≠ p.2)
    (by simp)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp [emb, a.2]

lemma mem_arcPolytope_iff {n : ℕ} (y : Arc n → ℝ) : y ∈ arcPolytope n ↔ emb y ∈ polytope n := by
  have hcol : ∀ j, ∑ a ∈ univ.filter (fun a : Arc n => a.1.2 = j), y a = ∑ i, emb y i j := by
    intro j; rw [arc_sum y (fun _ j' => j' = j)]
    refine Finset.sum_congr rfl (fun i _ => ?_); simp
  have hrow : ∀ i, ∑ a ∈ univ.filter (fun a : Arc n => a.1.1 = i), y a = ∑ j, emb y i j := by
    intro i; rw [arc_sum y (fun i' _ => i' = i)]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hcut : ∀ S : Finset (Fin n), ∑ a ∈ univ.filter (fun a : Arc n => a.1.1 ∈ S ∧ a.1.2 ∉ S), y a =
      flux (emb y) S := by
    intro S; rw [arc_sum y (fun i j => i ∈ S ∧ j ∉ S), ← flux_ite_expand_general]
  constructor
  · rintro ⟨h0, hc, hr, hS⟩
    refine ⟨fun i => by simp [emb], fun i j => ?_, fun j => by rw [← hcol]; exact hc j,
      fun i => by rw [← hrow]; exact hr i, fun S h2 h6 => by rw [← hcut]; exact hS S h2 h6⟩
    by_cases h : i = j
    · simp [emb, h]
    · simp only [emb, ne_eq, h, not_false_eq_true, dite_true]; exact h0 _
  · rintro ⟨_, h0, hc, hr, hS⟩
    refine ⟨fun a => ?_, fun j => by rw [hcol]; exact hc j, fun i => by rw [hrow]; exact hr i,
      fun S h2 h6 => by rw [hcut]; exact hS S h2 h6⟩
    have := h0 a.1.1 a.1.2; simpa [emb, a.2] using this

lemma res_add {n : ℕ} (x y : Fin n → Fin n → ℝ) : res (x + y) = res x + res y := rfl
lemma res_smul {n : ℕ} (c : ℝ) (x : Fin n → Fin n → ℝ) : res (c • x) = c • res x := rfl

lemma emb_arcTour {n : ℕ} (σ : Equiv.Perm (Fin n)) (hs : σ.support = Finset.univ) :
    emb (arcTour σ) = tourMatrix σ := by
  funext i j
  by_cases h : i = j
  · subst h
    have : σ i ≠ i := Equiv.Perm.mem_support.1 (by rw [hs]; exact Finset.mem_univ i)
    simp [emb, tourMatrix, this]
  · simp [emb, arcTour, tourMatrix, h]

lemma emb_segment {n : ℕ} (x t : Arc n → ℝ) : emb '' segment ℝ x t = segment ℝ (emb x) (emb t) := by
  ext z; constructor
  · rintro ⟨w, ⟨a, b, ha, hb, hab, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, hab, by rw [emb_add, emb_smul, emb_smul]⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨a • x + b • t, ⟨a, b, ha, hb, hab, rfl⟩, by rw [emb_add, emb_smul, emb_smul]⟩

/-- The arc-space vertex `x* ↾ A`. -/
noncomputable def xa : Arc 8 → ℝ := res xs

lemma emb_xa : emb xa = xs := emb_res xs xs_mem.1

theorem xa_extreme : xa ∈ Set.extremePoints ℝ (arcPolytope 8) := by
  rw [mem_extremePoints]
  refine ⟨(mem_arcPolytope_iff xa).2 (by rw [emb_xa]; exact xs_mem), fun y hy w hw hseg => ?_⟩
  have hE := xs_extreme
  rw [IsVertex, mem_extremePoints] at hE
  obtain ⟨a, b, ha, hb, hab, h⟩ := hseg
  have hseg' : xs ∈ openSegment ℝ (emb y) (emb w) :=
    ⟨a, b, ha, hb, hab, by rw [← emb_smul, ← emb_smul, ← emb_add, h, emb_xa]⟩
  obtain ⟨h1, h2⟩ := hE.2 (emb y) ((mem_arcPolytope_iff y).1 hy) (emb w) ((mem_arcPolytope_iff w).1 hw) hseg'
  exact ⟨emb_injective (h1.trans emb_xa.symm), emb_injective (h2.trans emb_xa.symm)⟩

theorem arc_segment_not_face (t : Arc 8 → ℝ) (ht : IsArcTour 8 t) :
    ¬ IsExtreme ℝ (arcPolytope 8) (segment ℝ xa t) := by
  obtain ⟨σ, hc, hs, rfl⟩ := ht
  intro hE
  apply segment_not_face (tourMatrix σ) ⟨σ, hc, hs, rfl⟩
  rw [← emb_xa, ← emb_arcTour σ hs, ← emb_segment]
  refine ⟨?_, fun p hp q hq z hz hzo => ?_⟩
  · rintro _ ⟨w, hw, rfl⟩; exact (mem_arcPolytope_iff w).1 (hE.1 hw)
  · obtain ⟨z', hz', rfl⟩ := hz
    have hp' : res p ∈ arcPolytope 8 := (mem_arcPolytope_iff _).2 (by rw [emb_res p hp.1]; exact hp)
    have hq' : res q ∈ arcPolytope 8 := (mem_arcPolytope_iff _).2 (by rw [emb_res q hq.1]; exact hq)
    have hzo' : z' ∈ openSegment ℝ (res p) (res q) := by
      obtain ⟨a, b, ha, hb, hab, h⟩ := hzo
      refine ⟨a, b, ha, hb, hab, ?_⟩
      rw [← res_smul, ← res_smul, ← res_add, h, res_emb]
    exact ⟨res p, hE.2 hp' hq' hz' hzo', emb_res p hp.1⟩

theorem arc_counterexample :
    xa ∈ Set.extremePoints ℝ (arcPolytope 8) ∧ ∀ t, IsArcTour 8 t → ¬ ArcAdjacent 8 xa t :=
  ⟨xa_extreme, fun t ht hadj => arc_segment_not_face t ht hadj.2.2.2⟩

/-- Conjecture 1 on the literal arc space is false. -/
theorem arc_neighborhood_tour_conjecture_false : ¬ ArcNeighborhoodTourConjecture := by
  intro h
  obtain ⟨t, ht, hadj⟩ := h 8 (by norm_num) xa xa_extreme
  exact arc_counterexample.2 t ht hadj

end ASEP

#print axioms ASEP.arc_counterexample
#print axioms ASEP.arc_neighborhood_tour_conjecture_false
