import Growth
import Mathlib.Data.Finset.Max
set_option autoImplicit false
namespace Polyomino57

def lowerCorner (P : Finset GridPoint) (h : P.Nonempty) : GridPoint :=
  ((P.image Prod.fst).min' (h.image _), (P.image Prod.snd).min' (h.image _))
def normalize (P : Finset GridPoint) (h : P.Nonempty) : Finset GridPoint :=
  translate (-(lowerCorner P h).1, -(lowerCorner P h).2) P

theorem translate_comp (s t : GridPoint) (P : Finset GridPoint) :
    translate s (translate t P) = translate (t.1+s.1,t.2+s.2) P := by
  simp only [translate, Finset.image_image]
  apply Finset.image_congr
  intro p _
  apply Prod.ext <;> dsimp <;> omega

theorem translate_zero (P : Finset GridPoint) : translate (0,0) P = P := by
  simp [translate]

theorem normalize_card (P : Finset GridPoint) (h : P.Nonempty) :
    (normalize P h).card = P.card := translate_card _ _

theorem normalize_connected {P : Finset GridPoint} (h : EdgeConnected P) :
    EdgeConnected (normalize P h.1) := translate_connected _ h

theorem normalize_nonnegative (P : Finset GridPoint) (h : P.Nonempty)
    (q : GridPoint) (hq : q ∈ normalize P h) : 0 ≤ q.1 ∧ 0 ≤ q.2 := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  have hx := Finset.min'_le (P.image Prod.fst) p.1 (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  have hy := Finset.min'_le (P.image Prod.snd) p.2 (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  change 0 ≤ p.1 + -((P.image Prod.fst).min' (h.image _)) ∧
    0 ≤ p.2 + -((P.image Prod.snd).min' (h.image _))
  omega

-- Recovery gives a literal equality even for sets crossing both coordinate axes.
theorem normalize_recover (P : Finset GridPoint) (h : P.Nonempty) :
    translate (lowerCorner P h) (normalize P h) = P := by
  rw [normalize,translate_comp]
  have hz : (-(lowerCorner P h).1+(lowerCorner P h).1,
    -(lowerCorner P h).2+(lowerCorner P h).2) = (0,0) := by
    ext <;> dsimp <;> omega
  rw [hz,translate_zero]

theorem equal_normalizations_are_translates (P Q : Finset GridPoint)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (h : normalize P hP = normalize Q hQ) :
    ∃ t : GridPoint, translate t P = Q := by
  refine ⟨((lowerCorner Q hQ).1-(lowerCorner P hP).1,
    (lowerCorner Q hQ).2-(lowerCorner P hP).2), ?_⟩
  have hr := normalize_recover Q hQ
  rw [← h,normalize,translate_comp] at hr
  convert hr using 1; congr 1; ext <;> dsimp <;> omega

theorem translate_nonempty (P : Finset GridPoint) (h : P.Nonempty) (t : GridPoint) :
    (translate t P).Nonempty := h.image _

theorem lowerCorner_translate (P : Finset GridPoint) (h : P.Nonempty) (t : GridPoint) :
    lowerCorner (translate t P) (translate_nonempty P h t) =
      ((lowerCorner P h).1+t.1,(lowerCorner P h).2+t.2) := by
  apply Prod.ext
  · apply (Finset.min'_eq_iff ((translate t P).image Prod.fst) ((translate_nonempty P h t).image _) _).mpr
    constructor
    · obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp (Finset.min'_mem (P.image Prod.fst) (h.image _))
      apply Finset.mem_image.mpr
      refine ⟨(p.1+t.1,p.2+t.2),Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
      change p.1+t.1 = (P.image Prod.fst).min' (h.image _) + t.1
      rw [heq]
    · intro x hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
      have hm := Finset.min'_le (P.image Prod.fst) p.1 (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
      change (P.image Prod.fst).min' (h.image _) + t.1 ≤ p.1+t.1
      omega
  · apply (Finset.min'_eq_iff ((translate t P).image Prod.snd) ((translate_nonempty P h t).image _) _).mpr
    constructor
    · obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp (Finset.min'_mem (P.image Prod.snd) (h.image _))
      apply Finset.mem_image.mpr
      refine ⟨(p.1+t.1,p.2+t.2),Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
      change p.2+t.2 = (P.image Prod.snd).min' (h.image _) + t.2
      rw [heq]
    · intro x hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
      have hm := Finset.min'_le (P.image Prod.snd) p.2 (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
      change (P.image Prod.snd).min' (h.image _) + t.2 ≤ p.2+t.2
      omega

theorem normalize_translate (P : Finset GridPoint) (h : P.Nonempty) (t : GridPoint) :
    normalize (translate t P) (translate_nonempty P h t) = normalize P h := by
  unfold normalize
  rw [lowerCorner_translate P h t, translate_comp]
  apply Finset.image_congr
  intro p _
  apply Prod.ext <;> dsimp <;> omega

theorem normalize_iff_translate (P Q : Finset GridPoint) (hP : P.Nonempty) (hQ : Q.Nonempty) :
    normalize P hP = normalize Q hQ ↔ ∃ t : GridPoint, translate t P = Q := by
  constructor
  · exact equal_normalizations_are_translates P Q hP hQ
  · rintro ⟨t,rfl⟩
    exact (normalize_translate P hP t).symm
end Polyomino57
