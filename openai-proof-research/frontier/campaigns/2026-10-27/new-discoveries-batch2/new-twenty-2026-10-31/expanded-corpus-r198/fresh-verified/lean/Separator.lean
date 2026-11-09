import Mathlib.Data.Finset.Powerset
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
open scoped BigOperators
namespace Separation
abbrev Point (d : ℕ) := Finset (Finset (Fin d))
def allowed {d : ℕ} (r : ℕ) (P : Point d) := ∀ S ∈ P, S.card ≤ r
def phi {d : ℕ} (r : ℕ) (X : Finset (Fin d)) : Point d := X.powerset.filter (fun S => S.card ≤ r)
def Separator (d r : ℕ) (f : Point d → ℤ) : Prop :=
 (∀ P Q, allowed r P → allowed r Q → f (P ∪ Q) + f (P ∩ Q) ≤ f P + f Q) ∧
 (∀ X, f (phi r X) ≤ -1) ∧
 (∀ P, allowed r P → (¬ ∃ X, phi r X = P) → 0 ≤ f P)
def SeparationExistence : Prop := ∀ d r : ℕ, r ≤ d → ∃ f, Separator d r f

def rename {d : ℕ} (s : Equiv.Perm (Fin d)) (P : Point d) : Point d := P.image (fun X => X.image s)
def avg {d : ℕ} (f : Point d → ℤ) (P : Point d) : ℤ := ∑ s : Equiv.Perm (Fin d), f (rename s P)
lemma rename_comp {d : ℕ} (s t : Equiv.Perm (Fin d)) (P : Point d) :
 rename s (rename t P) = rename (s * t) P := by
 simp [rename, Finset.image_image, Function.comp_def]
lemma avg_rename {d : ℕ} (f : Point d → ℤ) (t : Equiv.Perm (Fin d)) (P : Point d) :
 avg f (rename t P) = avg f P := by
 simp only [avg, rename_comp]
 exact Fintype.sum_equiv (Equiv.mulRight t) _ _ (fun s => rfl)

lemma rename_inj {d : ℕ} (s : Equiv.Perm (Fin d)) : Function.Injective (fun X : Finset (Fin d) => X.image s) :=
 Finset.image_injective s.injective
lemma allowed_rename {d r : ℕ} (s : Equiv.Perm (Fin d)) (P : Point d) (h : allowed r P) : allowed r (rename s P) := by
 intro X hX
 obtain ⟨Y,hY,rfl⟩ := Finset.mem_image.mp hX
 simpa [Finset.card_image_of_injective, s.injective] using h Y hY
lemma rename_phi {d r : ℕ} (s : Equiv.Perm (Fin d)) (X : Finset (Fin d)) :
 rename s (phi r X) = phi r (X.image s) := by
 simp only [rename, phi, Finset.powerset_image]
 rw [Finset.filter_image]
 simp only [Finset.card_image_of_injective, s.injective]
lemma rename_one {d : ℕ} (P : Point d) : rename 1 P = P := by
 simp [rename]
lemma rename_inverse {d : ℕ} (s : Equiv.Perm (Fin d)) (P : Point d) : rename s⁻¹ (rename s P) = P := by
 rw [rename_comp, inv_mul_cancel, rename_one]
lemma avg_submod {d r : ℕ} (f : Point d → ℤ) (hf : Separator d r f) (P Q : Point d)
 (hP : allowed r P) (hQ : allowed r Q) :
 avg f (P ∪ Q) + avg f (P ∩ Q) ≤ avg f P + avg f Q := by
 simp only [avg, ← Finset.sum_add_distrib]
 apply Finset.sum_le_sum
 intro s _
 have h := hf.1 (rename s P) (rename s Q) (allowed_rename s P hP) (allowed_rename s Q hQ)
 simpa only [rename, Finset.image_union, Finset.image_inter P Q (rename_inj s)] using h
lemma avg_good {d r : ℕ} (f : Point d → ℤ) (hf : Separator d r f) (X : Finset (Fin d)) :
 avg f (phi r X) ≤ -(Fintype.card (Equiv.Perm (Fin d)) : ℤ) := by
 calc
  avg f (phi r X) ≤ ∑ _s : Equiv.Perm (Fin d), (-1 : ℤ) := by
   apply Finset.sum_le_sum
   intro s _
   rw [rename_phi]
   exact hf.2.1 _
  _ = _ := by simp
lemma avg_bad {d r : ℕ} (f : Point d → ℤ) (hf : Separator d r f) (P : Point d)
 (hP : allowed r P) (hbad : ¬ ∃ X, phi r X = P) : 0 ≤ avg f P := by
 apply Finset.sum_nonneg
 intro s _
 apply hf.2.2 _ (allowed_rename s P hP)
 rintro ⟨X,hX⟩
 apply hbad
 refine ⟨X.image ((s⁻¹ : Equiv.Perm (Fin d)) : Fin d → Fin d), ?_⟩
 rw [← rename_phi, hX, rename_inverse]
end Separation
