import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push
import Aesop
set_option maxRecDepth 4096
set_option maxHeartbeats 10000000
namespace Circulant350979
abbrev V := Fin 15
-- A simple path is indexed in order; the iff says precisely that it is induced.
def InducedPath {V : Type} (R : V → V → Prop) (m : ℕ) (f : Fin (m+1) → V) : Prop :=
  Function.Injective f ∧ ∀ i j, R (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

def TripleMP {V : Type} (R : V → V → Prop) (a b c : V) : Prop :=
  ∀ m f, InducedPath R m f → ¬ ∃ i j k, f i = a ∧ f j = b ∧ f k = c

lemma triangle_mp {V : Type} {R : V → V → Prop} {a b c : V}
    (ab : R a b) (ac : R a c) (bc : R b c) : TripleMP R a b c := by
  intro m f hp ⟨i,j,k,hi,hj,hk⟩
  have h1 := (hp.2 i j).mp (by simpa [hi,hj] using ab)
  have h2 := (hp.2 i k).mp (by simpa [hi,hk] using ac)
  have h3 := (hp.2 j k).mp (by simpa [hj,hk] using bc)
  omega

lemma twins_mp {V : Type} {R : V → V → Prop} {a b c : V}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (hab : ∀ v, R a v ↔ R b v) (hac : ∀ v, R a v ↔ R c v) : TripleMP R a b c := by
  intro m f hp ⟨i,j,k,hi,hj,hk⟩
  have hij : i.val ≠ j.val := by intro h; have : i=j := Fin.ext h; subst j; exact ab (hi.symm.trans hj)
  have hik : i.val ≠ k.val := by intro h; have : i=k := Fin.ext h; subst k; exact ac (hi.symm.trans hk)
  have hjk : j.val ≠ k.val := by intro h; have : j=k := Fin.ext h; subst k; exact bc (hj.symm.trans hk)
  have hm : 0 < m := by have := i.isLt; have := j.isLt; omega
  have neighbor : ∃ q : Fin (m+1), R a (f q) := by
    by_cases h : i.val < m
    · refine ⟨⟨i.val+1, by omega⟩, ?_⟩
      rw [← hi]; exact (hp.2 i _).mpr (Or.inl rfl)
    · refine ⟨⟨i.val-1, by omega⟩, ?_⟩
      rw [← hi]; apply (hp.2 i _).mpr; right; dsimp; omega
  obtain ⟨q,hq⟩ := neighbor
  have h1 := (hp.2 i q).mp (by simpa [hi] using hq)
  have h2 := (hp.2 j q).mp (by simpa [hj] using (hab _).mp hq)
  have h3 := (hp.2 k q).mp (by simpa [hk] using (hac _).mp hq)
  omega

-- Bit d selects the cyclic difference ±(d+1), d=0,...,6.
def adj (s : Fin 128) (a b : V) : Prop :=
  ∃ d : Fin 7, s.val.testBit d.val = true ∧
    ((a.val + d.val + 1) % 15 = b.val ∨ (b.val + d.val + 1) % 15 = a.val)
instance (s : Fin 128) (a b : V) : Decidable (adj s a b) := inferInstanceAs (Decidable (∃ d : Fin 7, s.val.testBit d.val = true ∧ ((a.val+d.val+1)%15=b.val ∨ (b.val+d.val+1)%15=a.val)))

def TriangleFreeAtZero (s : Fin 128) : Prop :=
  ∀ a b : V, ¬ (adj s 0 a ∧ adj s 0 b ∧ adj s a b)
def RadiusTwoAtZero (s : Fin 128) : Prop :=
  ∀ b : V, b = 0 ∨ adj s 0 b ∨ ∃ c : V, adj s 0 c ∧ adj s c b
instance (s) : Decidable (TriangleFreeAtZero s) := inferInstanceAs (Decidable (∀ a b : V, ¬ (adj s 0 a ∧ adj s 0 b ∧ adj s a b)))
instance (s) : Decidable (RadiusTwoAtZero s) := inferInstanceAs (Decidable (∀ b : V, b = 0 ∨ adj s 0 b ∨ ∃ c : V, adj s 0 c ∧ adj s c b))

-- Complete enumeration of all 128 undirected circulants of order 15.
theorem classify : ∀ s : Fin 128,
    TriangleFreeAtZero s → RadiusTwoAtZero s → s = 41 ∨ s = 70 := by decide

theorem twins41 : ∀ v : V, (adj 41 0 v ↔ adj 41 5 v) ∧ (adj 41 0 v ↔ adj 41 10 v) := by decide
theorem twins70 : ∀ v : V, (adj 70 0 v ↔ adj 70 5 v) ∧ (adj 70 0 v ↔ adj 70 10 v) := by decide

theorem obstruction (s : Fin 128) (hd : RadiusTwoAtZero s) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ TripleMP (adj s) a b c := by
  by_cases ht : TriangleFreeAtZero s
  · rcases classify s ht hd with rfl | rfl
    · exact ⟨0,5,10, by decide, by decide, by decide,
        twins_mp (by decide) (by decide) (by decide) (fun v => (twins41 v).1) (fun v => (twins41 v).2)⟩
    · exact ⟨0,5,10, by decide, by decide, by decide,
        twins_mp (by decide) (by decide) (by decide) (fun v => (twins70 v).1) (fun v => (twins70 v).2)⟩
  · unfold TriangleFreeAtZero at ht
    push Not at ht
    obtain ⟨a,b,h0a,h0b,hab⟩ := ht
    have hdiag : ∀ v : V, ¬ adj s v v := by
      intro v ⟨d,_,h⟩; rcases h with h | h <;> have := v.isLt <;> have := d.isLt <;> omega
    exact ⟨0,a,b,(by intro h; subst a; exact hdiag 0 h0a),
      (by intro h; subst b; exact hdiag 0 h0b),
      (by intro h; subst b; exact hdiag a hab), triangle_mp h0a h0b hab⟩
end Circulant350979
