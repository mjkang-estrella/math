module
public import URMatchingAvoidanceBound
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Powerset
@[expose] public section
namespace URMatching
open scoped Classical
/-- Pairs of actual a-element subsets, without an assumed hole condition. -/
abbrev Rectangles (N a : ℕ) :=
  {R : Finset (Fin N) × Finset (Fin N) // R.1.card = a ∧ R.2.card = a}
noncomputable def holeEvent (N a : ℕ) : Finset (PermutationTuples N 100) :=
  Finset.univ.filter fun f => ∃ R : Rectangles N a, ∀ c,
    AvoidsRectangle R.val.1 R.val.2 (f c)

theorem rectangle_choices_bound (N a : ℕ) :
    Fintype.card (Rectangles N a) ≤ 4 ^ N := by
  classical
  calc
    _ ≤ Fintype.card (Finset (Fin N) × Finset (Fin N)) := Fintype.card_subtype_le _
    _ = _ := by simp [← mul_pow]

/-- Finite union bound, kept in integer form for exact probability comparison. -/
theorem scaled_union_card {ι Ω : Type*} [DecidableEq Ω]
    (s : Finset ι) (E : ι → Finset Ω) (q r : ℕ)
    (h : ∀ i ∈ s, q * (E i).card ≤ r) :
    q * (s.biUnion E).card ≤ s.card * r := by
  have hs : q * (∑ i ∈ s, (E i).card) ≤ s.card * r := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.mul_add, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))) |>.trans_eq (Nat.add_comm _ _)
  exact (Nat.mul_le_mul_left q Finset.card_biUnion_le).trans hs

/-- All rectangles union bound on 100 independent permutations of 4a labels. -/
theorem hole_union_bound (a : ℕ) :
    (4 ^ a) ^ 100 * (holeEvent (4 * a) a).card ≤
      4 ^ (4 * a) * ((3 ^ a) ^ 100 * (4 * a).factorial ^ 100) := by
  classical
  let E (R : Rectangles (4 * a) a) : Finset (PermutationTuples (4 * a) 100) :=
    Finset.univ.filter fun f => ∀ c, AvoidsRectangle R.val.1 R.val.2 (f c)
  have hu : holeEvent (4 * a) a = Finset.univ.biUnion E := by
    ext f
    simp [holeEvent, E]
  have he (R : Rectangles (4 * a) a) :
      (4 ^ a) ^ 100 * (E R).card ≤ (3 ^ a) ^ 100 * (4 * a).factorial ^ 100 := by
    have h := hundred_colour_avoidance_bound R.val.1 R.val.2
      (by rw [R.property.1, R.property.2]; omega)
      (by rw [R.property.2])
    simpa only [E, ← Fintype.card_subtype, R.property.1] using h
  rw [hu]
  exact (scaled_union_card Finset.univ E _ _ (fun R _ => he R)).trans
    (Nat.mul_le_mul_right _ (by simpa using rectangle_choices_bound (4*a) a))
/-- A rational geometric estimate suffices; no exponential analysis is needed. -/
theorem hole_geometric_strict (a : ℕ) (ha : 0 < a) :
    4 * (4 ^ (4 * a) * (3 ^ a) ^ 100) < (4 ^ a) ^ 100 := by
  have hsmall : 4 * (4 ^ 4 * 3 ^ 100) < 4 ^ 100 := by decide
  have hbase : 4 ^ 4 * 3 ^ 100 < 4 ^ 100 := by omega
  have hp : 4 * (4 ^ 4 * 3 ^ 100) ^ a < (4 ^ 100) ^ a := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    calc
      _ = (4 * (4 ^ 4 * 3 ^ 100)) * (4 ^ 4 * 3 ^ 100) ^ k := by
        rw [pow_succ _ k]; ac_rfl
      _ < (4 ^ 100) * (4 ^ 4 * 3 ^ 100) ^ k :=
        Nat.mul_lt_mul_of_pos_right hsmall (Nat.pow_pos (by decide))
      _ ≤ (4 ^ 100) * (4 ^ 100) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_of_lt hbase) _)
      _ = _ := by rw [pow_succ _ k]; ac_rfl
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm a 100] using hp

/-- Strictly fewer than one quarter of all tuples have an a-square hole, a>0. -/
theorem strict_hole_estimate (a : ℕ) (ha : 0 < a) :
    4 * (holeEvent (4 * a) a).card < Fintype.card (PermutationTuples (4 * a) 100) := by
  have h := hole_union_bound a
  have hs := hole_geometric_strict a ha
  have hf : 0 < (4 * a).factorial ^ 100 := Nat.pow_pos (Nat.factorial_pos _)
  have ht : Fintype.card (PermutationTuples (4 * a) 100) = (4 * a).factorial ^ 100 := by
    simp [PermutationTuples, Fintype.card_perm]
  rw [ht]
  apply Nat.lt_of_mul_lt_mul_left (a := (4 ^ a) ^ 100)
  calc
    _ = 4 * ((4 ^ a) ^ 100 * (holeEvent (4 * a) a).card) := by ac_rfl
    _ ≤ 4 * (4 ^ (4 * a) * ((3 ^ a) ^ 100 * (4 * a).factorial ^ 100)) :=
      Nat.mul_le_mul_left 4 h
    _ = (4 * (4 ^ (4 * a) * (3 ^ a) ^ 100)) * (4 * a).factorial ^ 100 := by ac_rfl
    _ < _ := Nat.mul_lt_mul_of_pos_right hs hf
/-- There is an actual unconditioned tuple with no a-square hole.
This does not impose or assert any short-cycle bound. -/
theorem exists_no_large_hole (a : ℕ) (ha : 0 < a) :
    ∃ f : PermutationTuples (4*a) 100,
      ∀ A B : Finset (Fin (4*a)), A.card = a → B.card = a →
        ∃ c, ∃ x ∈ A, f c x ∈ B := by
  classical
  have hs := strict_hole_estimate a ha
  have hex : ∃ f : PermutationTuples (4*a) 100, f ∉ holeEvent (4*a) a := by
    by_contra h
    have hu : holeEvent (4*a) a = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro f
      by_contra hf
      exact h ⟨f, hf⟩
    rw [hu, Finset.card_univ] at hs
    omega
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, fun A B hA hB => ?_⟩
  by_contra h
  apply hf
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ f, ⟨⟨(A,B), hA, hB⟩, ?_⟩⟩
  intro c x hx hB'
  exact h ⟨c, x, hx, hB'⟩
end URMatching
