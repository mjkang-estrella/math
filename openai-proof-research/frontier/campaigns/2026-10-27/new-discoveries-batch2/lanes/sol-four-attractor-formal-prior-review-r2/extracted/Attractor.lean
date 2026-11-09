import Words
import Geometry
import Mathlib.Data.Finset.Card
set_option autoImplicit false
set_option warningAsError true
namespace FourAttractor
def Occurs (s f : Word) (i : Nat) : Prop := i + f.length ≤ s.length ∧ (s.drop i).take f.length = f
instance (s f : Word) (i : Nat) : Decidable (Occurs s f i) := inferInstanceAs (Decidable (_ ∧ _))
def Attractor (s : Word) (g : Finset (Fin s.length)) : Prop :=
  ∀ f : Word, f ≠ [] → (∃ i, Occurs s f i) →
    ∃ j, Occurs s f j ∧ ∃ p ∈ g, j ≤ p.val ∧ p.val < j + f.length
theorem coverFour {α : Type} [Inhabited α] (l : List α) (h : l.length ≤ 4) :
    ∃ a b c d : α, ∀ x ∈ l, x = a ∨ x = b ∨ x = c ∨ x = d := by
  cases l with
  | nil => exact ⟨default, default, default, default, by simp⟩
  | cons a l =>
    cases l with
    | nil => exact ⟨a,a,a,a, by simp⟩
    | cons b l =>
      cases l with
      | nil => exact ⟨a,b,b,b, by simp_all⟩
      | cons c l =>
        cases l with
        | nil => exact ⟨a,b,c,c, by simp_all⟩
        | cons d l =>
          cases l with
          | nil => exact ⟨a,b,c,d, by simp_all⟩
          | cons e l => simp at h
theorem occurrences1 : ∀ i : Fin 37, Occurs w (bits "001010") i.val ↔ i.val = 5 := by decide
 theorem necessary1 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 5 10 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "001010") (by decide) ⟨5, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 6 ≤ 36 at this; omega
  have hs := (occurrences1 ⟨j,jb⟩).mp hj
  change j = 5 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 6 at hr
  simp only [inI]
  omega
theorem occurrences2 : ∀ i : Fin 37, Occurs w (bits "010101") i.val ↔ i.val = 6 := by decide
 theorem necessary2 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 6 11 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "010101") (by decide) ⟨6, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 6 ≤ 36 at this; omega
  have hs := (occurrences2 ⟨j,jb⟩).mp hj
  change j = 6 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 6 at hr
  simp only [inI]
  omega
theorem occurrences3 : ∀ i : Fin 37, Occurs w (bits "101011") i.val ↔ i.val = 7 := by decide
 theorem necessary3 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 7 12 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "101011") (by decide) ⟨7, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 6 ≤ 36 at this; omega
  have hs := (occurrences3 ⟨j,jb⟩).mp hj
  change j = 7 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 6 at hr
  simp only [inI]
  omega
theorem occurrences4 : ∀ i : Fin 37, Occurs w (bits "001011") i.val ↔ i.val = 13 := by decide
 theorem necessary4 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 13 18 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "001011") (by decide) ⟨13, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 6 ≤ 36 at this; omega
  have hs := (occurrences4 ⟨j,jb⟩).mp hj
  change j = 13 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 6 at hr
  simp only [inI]
  omega
theorem occurrences5 : ∀ i : Fin 37, Occurs w (bits "101101") i.val ↔ i.val = 15 := by decide
 theorem necessary5 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 15 20 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "101101") (by decide) ⟨15, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 6 ≤ 36 at this; omega
  have hs := (occurrences5 ⟨j,jb⟩).mp hj
  change j = 15 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 6 at hr
  simp only [inI]
  omega
theorem occurrences6 : ∀ i : Fin 37, Occurs w (bits "110100") i.val ↔ i.val = 17 := by decide
 theorem necessary6 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 17 22 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "110100") (by decide) ⟨17, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 6 ≤ 36 at this; omega
  have hs := (occurrences6 ⟨j,jb⟩).mp hj
  change j = 17 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 6 at hr
  simp only [inI]
  omega
theorem occurrences7 : ∀ i : Fin 37, Occurs w (bits "110101") i.val ↔ i.val = 23 := by decide
 theorem necessary7 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 23 28 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "110101") (by decide) ⟨23, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 6 ≤ 36 at this; omega
  have hs := (occurrences7 ⟨j,jb⟩).mp hj
  change j = 23 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 6 at hr
  simp only [inI]
  omega
theorem occurrences8 : ∀ i : Fin 37, Occurs w (bits "101010") i.val ↔ i.val = 24 := by decide
 theorem necessary8 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 24 29 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "101010") (by decide) ⟨24, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 6 ≤ 36 at this; omega
  have hs := (occurrences8 ⟨j,jb⟩).mp hj
  change j = 24 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 6 at hr
  simp only [inI]
  omega
theorem occurrences9 : ∀ i : Fin 37, Occurs w (bits "010100") i.val ↔ i.val = 25 := by decide
 theorem necessary9 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 25 30 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "010100") (by decide) ⟨25, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 6 ≤ 36 at this; omega
  have hs := (occurrences9 ⟨j,jb⟩).mp hj
  change j = 25 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 6 at hr
  simp only [inI]
  omega
theorem occurrences10 : ∀ i : Fin 37, Occurs w (bits "1100") i.val ↔ i.val = 3 ∨ i.val = 11 := by decide
 theorem necessary10 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 3 6 ∨ inI p.val 11 14 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "1100") (by decide) ⟨3, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 4 ≤ 36 at this; omega
  have hs := (occurrences10 ⟨j,jb⟩).mp hj
  change j = 3 ∨ j = 11 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 4 at hr
  simp only [inI]
  omega
theorem occurrences11 : ∀ i : Fin 37, Occurs w (bits "0011") i.val ↔ i.val = 21 ∨ i.val = 29 := by decide
 theorem necessary11 (g : Finset (Fin w.length)) (hg : Attractor w g) :
    ∃ p ∈ g, inI p.val 21 24 ∨ inI p.val 29 32 := by
  obtain ⟨j, hj, p, hp, hl, hr⟩ := hg (bits "0011") (by decide) ⟨21, by decide⟩
  have jb : j < 37 := by have := hj.1; change j + 4 ≤ 36 at this; omega
  have hs := (occurrences11 ⟨j,jb⟩).mp hj
  change j = 21 ∨ j = 29 at hs
  refine ⟨p, hp, ?_⟩
  change j ≤ p.val at hl
  change p.val < j + 4 at hr
  simp only [inI]
  omega
end FourAttractor
