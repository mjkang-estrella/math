module
public import GridFinal6
public import GridRegression
@[expose] public section
open Grid343536
namespace FidelitySanity
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def labels_1_1 : List (List ℕ) := [[0]]
example : labels_1_1.Nodup := by decide
example : labels_1_1.length = 1 := by decide
example : labels_1_1.all (fun lab => decide (labelEquitable 1 1 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 1 1 lab) :
    ∃ H : Subgroup (G 1 1 ≃g G 1 1), labelSetoid 1 1 lab = orbitSetoid (G 1 1) H :=
  ((GridFinal6.mathdb_343536 1 1 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : HasFreeVertex (G 1 1) := by
  apply (free_classification 1 1 (by decide) (by decide)).mpr
  decide
def labels_1_2 : List (List ℕ) := [[0, 0], [0, 1]]
example : labels_1_2.Nodup := by decide
example : labels_1_2.length = 2 := by decide
example : labels_1_2.all (fun lab => decide (labelEquitable 1 2 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 1 2 lab) :
    ∃ H : Subgroup (G 1 2 ≃g G 1 2), labelSetoid 1 2 lab = orbitSetoid (G 1 2) H :=
  ((GridFinal6.mathdb_343536 1 2 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : HasFreeVertex (G 1 2) := by
  apply (free_classification 1 2 (by decide) (by decide)).mpr
  decide
def labels_1_3 : List (List ℕ) := [[0, 1, 0], [0, 1, 2]]
example : labels_1_3.Nodup := by decide
example : labels_1_3.length = 2 := by decide
example : labels_1_3.all (fun lab => decide (labelEquitable 1 3 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 1 3 lab) :
    ∃ H : Subgroup (G 1 3 ≃g G 1 3), labelSetoid 1 3 lab = orbitSetoid (G 1 3) H :=
  ((GridFinal6.mathdb_343536 1 3 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : HasFreeVertex (G 1 3) := by
  apply (free_classification 1 3 (by decide) (by decide)).mpr
  decide
def labels_1_4 : List (List ℕ) := [[0, 1, 1, 0], [0, 1, 2, 3]]
example : labels_1_4.Nodup := by decide
example : labels_1_4.length = 2 := by decide
example : labels_1_4.all (fun lab => decide (labelEquitable 1 4 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 1 4 lab) :
    ∃ H : Subgroup (G 1 4 ≃g G 1 4), labelSetoid 1 4 lab = orbitSetoid (G 1 4) H :=
  ((GridFinal6.mathdb_343536 1 4 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : HasFreeVertex (G 1 4) := by
  apply (free_classification 1 4 (by decide) (by decide)).mpr
  decide
def labels_1_5 : List (List ℕ) := [[0, 1, 2, 1, 0], [0, 1, 2, 3, 4]]
example : labels_1_5.Nodup := by decide
example : labels_1_5.length = 2 := by decide
example : labels_1_5.all (fun lab => decide (labelEquitable 1 5 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 1 5 lab) :
    ∃ H : Subgroup (G 1 5 ≃g G 1 5), labelSetoid 1 5 lab = orbitSetoid (G 1 5) H :=
  ((GridFinal6.mathdb_343536 1 5 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : HasFreeVertex (G 1 5) := by
  apply (free_classification 1 5 (by decide) (by decide)).mpr
  decide
def labels_1_6 : List (List ℕ) := [[0, 1, 2, 2, 1, 0], [0, 1, 2, 3, 4, 5]]
example : labels_1_6.Nodup := by decide
example : labels_1_6.length = 2 := by decide
example : labels_1_6.all (fun lab => decide (labelEquitable 1 6 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 1 6 lab) :
    ∃ H : Subgroup (G 1 6 ≃g G 1 6), labelSetoid 1 6 lab = orbitSetoid (G 1 6) H :=
  ((GridFinal6.mathdb_343536 1 6 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : HasFreeVertex (G 1 6) := by
  apply (free_classification 1 6 (by decide) (by decide)).mpr
  decide
def labels_2_2 : List (List ℕ) := [[0, 0, 0, 0], [0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 0], [0, 1, 1, 2], [0, 1, 2, 0], [0, 1, 2, 3]]
example : labels_2_2.Nodup := by decide
example : labels_2_2.length = 7 := by decide
example : labels_2_2.all (fun lab => decide (labelEquitable 2 2 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 2 2 lab) :
    ∃ H : Subgroup (G 2 2 ≃g G 2 2), labelSetoid 2 2 lab = orbitSetoid (G 2 2) H :=
  ((GridFinal6.mathdb_343536 2 2 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : ¬ HasFreeVertex (G 2 2) := by
  intro h; have hbad : ¬ (2 ≤ 2 ∧ 2 = 2 ∧ 2 ≤ 3) := (free_classification 2 2 (by decide) (by decide)).mp h
  exact hbad (by decide)
def labels_2_3 : List (List ℕ) := [[0, 1, 0, 0, 1, 0], [0, 1, 0, 2, 3, 2], [0, 1, 2, 0, 1, 2], [0, 1, 2, 2, 1, 0], [0, 1, 2, 3, 4, 5]]
example : labels_2_3.Nodup := by decide
example : labels_2_3.length = 5 := by decide
example : labels_2_3.all (fun lab => decide (labelEquitable 2 3 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 2 3 lab) :
    ∃ H : Subgroup (G 2 3 ≃g G 2 3), labelSetoid 2 3 lab = orbitSetoid (G 2 3) H :=
  ((GridFinal6.mathdb_343536 2 3 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : HasFreeVertex (G 2 3) := by
  apply (free_classification 2 3 (by decide) (by decide)).mpr
  decide
def labels_3_3 : List (List ℕ) := [[0, 1, 0, 1, 2, 1, 0, 1, 0], [0, 1, 0, 2, 3, 2, 0, 1, 0], [0, 1, 0, 2, 3, 2, 4, 5, 4], [0, 1, 2, 1, 3, 1, 2, 1, 0], [0, 1, 2, 1, 3, 4, 2, 4, 5], [0, 1, 2, 3, 4, 1, 5, 3, 0], [0, 1, 2, 3, 4, 3, 2, 1, 0], [0, 1, 2, 3, 4, 5, 0, 1, 2], [0, 1, 2, 3, 4, 5, 6, 7, 8]]
example : labels_3_3.Nodup := by decide
example : labels_3_3.length = 9 := by decide
example : labels_3_3.all (fun lab => decide (labelEquitable 3 3 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 3 3 lab) :
    ∃ H : Subgroup (G 3 3 ≃g G 3 3), labelSetoid 3 3 lab = orbitSetoid (G 3 3) H :=
  ((GridFinal6.mathdb_343536 3 3 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : ¬ HasFreeVertex (G 3 3) := by
  intro h; have hbad : ¬ (2 ≤ 3 ∧ 3 = 3 ∧ 3 ≤ 3) := (free_classification 3 3 (by decide) (by decide)).mp h
  exact hbad (by decide)
def labels_3_4 : List (List ℕ) := [[0, 1, 1, 0, 2, 3, 3, 2, 0, 1, 1, 0], [0, 1, 1, 0, 2, 3, 3, 2, 4, 5, 5, 4], [0, 1, 2, 3, 4, 5, 5, 4, 3, 2, 1, 0], [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
example : labels_3_4.Nodup := by decide
example : labels_3_4.length = 5 := by decide
example : labels_3_4.all (fun lab => decide (labelEquitable 3 4 lab)) = true := by decide
example (lab : List ℕ) (h : labelEquitable 3 4 lab) :
    ∃ H : Subgroup (G 3 4 ≃g G 3 4), labelSetoid 3 4 lab = orbitSetoid (G 3 4) H :=
  ((GridFinal6.mathdb_343536 3 4 (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)
example : HasFreeVertex (G 3 4) := by
  apply (free_classification 3 4 (by decide) (by decide)).mpr
  decide
example : ¬ Nonempty (EqPart (G 2 2) ≃o Subgroup (G 2 2 ≃g G 2 2)) := exceptional_no_iso 2 (by decide) (by decide)
example : ¬ Nonempty (EqPart (G 3 3) ≃o Subgroup (G 3 3 ≃g G 3 3)) := exceptional_no_iso 3 (by decide) (by decide)
example : HasFreeVertex (G 4 4) := (free_classification 4 4 (by decide) (by decide)).mpr (by decide)
example : ¬ IsEquitable (G 3 4) (labelSetoid 3 4 [0,0,0,0,0,0,0,0,0,0,0,0]) := by
  rw [labelEquitable_iff]; decide
example : (⊥ : Setoid (Fin 3 × Fin 4)) ≤ ⊤ := bot_le
example (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : NaturalLatticeIso m n ↔ HasFreeVertex (G m n) :=
  natural_iso_iff main_orbit_proved free_classification exceptional_no_iso m n hm hn
#print axioms GridFinal6.mathdb_343536
def color (m n : ℕ) (lab : List ℕ) (x : Fin m × Fin n) : ℕ := lab[x.1.val*n+x.2.val]?.getD 0
def witnessCheck (m n k : ℕ) (autos : Fin k → (G m n ≃g G m n)) (lab : List ℕ) : Prop :=
  ∀ u v : Fin m × Fin n, color m n lab u = color m n lab v ↔
    ∃ i : Fin k, (∀ x, color m n lab (autos i x) = color m n lab x) ∧ autos i u = v
instance witnessDec (m n k : ℕ) (autos : Fin k → (G m n ≃g G m n)) (lab : List ℕ) : Decidable (witnessCheck m n k autos lab) := by
  unfold witnessCheck; infer_instance
example : labels_1_1.all (fun lab => decide (witnessCheck 1 1 8 (sym8 1) lab)) = true := by decide
example : labels_1_2.all (fun lab => decide (witnessCheck 1 2 4 (![1, rowFlip 1 2, colFlip 1 2, rowFlip 1 2 * colFlip 1 2]) lab)) = true := by decide
example : labels_1_3.all (fun lab => decide (witnessCheck 1 3 4 (![1, rowFlip 1 3, colFlip 1 3, rowFlip 1 3 * colFlip 1 3]) lab)) = true := by decide
example : labels_1_4.all (fun lab => decide (witnessCheck 1 4 4 (![1, rowFlip 1 4, colFlip 1 4, rowFlip 1 4 * colFlip 1 4]) lab)) = true := by decide
example : labels_1_5.all (fun lab => decide (witnessCheck 1 5 4 (![1, rowFlip 1 5, colFlip 1 5, rowFlip 1 5 * colFlip 1 5]) lab)) = true := by decide
example : labels_1_6.all (fun lab => decide (witnessCheck 1 6 4 (![1, rowFlip 1 6, colFlip 1 6, rowFlip 1 6 * colFlip 1 6]) lab)) = true := by decide
example : labels_2_2.all (fun lab => decide (witnessCheck 2 2 8 (sym8 2) lab)) = true := by decide
example : labels_2_3.all (fun lab => decide (witnessCheck 2 3 4 (![1, rowFlip 2 3, colFlip 2 3, rowFlip 2 3 * colFlip 2 3]) lab)) = true := by decide
example : labels_3_3.all (fun lab => decide (witnessCheck 3 3 8 (sym8 3) lab)) = true := by decide
example : labels_3_4.all (fun lab => decide (witnessCheck 3 4 4 (![1, rowFlip 3 4, colFlip 3 4, rowFlip 3 4 * colFlip 3 4]) lab)) = true := by decide
end FidelitySanity
