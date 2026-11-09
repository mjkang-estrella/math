import BergmanResidues

open Finset
namespace BergmanUnitCircle

lemma finite_fiber_gram {I J : Type*} [DecidableEq I] [DecidableEq J]
    (s : Finset I) (t : Finset J) (f : I → J) (w : I → ℂ)
    (hf : ∀ x ∈ s, f x ∈ t) :
    (∑ x ∈ s, ∑ y ∈ s, if f x=f y then w x*star (w y) else 0) =
    ∑ r ∈ t, (∑ x ∈ s with f x=r, w x)*star (∑ x ∈ s with f x=r, w x) := by
  have hi (x : I) : (∑ y ∈ s, if f x=f y then w x*star (w y) else 0) =
      w x*(∑ y ∈ s with f y=f x, star (w y)) := by
    rw [mul_sum]
    simp only [sum_filter]
    apply sum_congr rfl
    intro y _
    by_cases he : f x=f y
    · simp [he]
    · have he' : f y≠f x := Ne.symm he
      simp [he,he']
  simp_rw [hi]
  rw [← sum_fiberwise_of_maps_to hf]
  apply sum_congr rfl
  intro r _
  calc
    (∑ x ∈ s with f x=r, w x*(∑ y ∈ s with f y=f x, star (w y))) =
        ∑ x ∈ s with f x=r, w x*(∑ y ∈ s with f y=r, star (w y)) := by
      apply sum_congr rfl
      intro x hx
      rw [(mem_filter.mp hx).2]
    _ = (∑ x ∈ s with f x=r, w x)*(∑ y ∈ s with f y=r, star (w y)) := by
      rw [sum_mul]
    _ = (∑ x ∈ s with f x=r, w x)*star (∑ y ∈ s with f y=r, w y) := by
      simp

lemma four_sum_gram {m n : ℕ} (hmn : n < m) (z : ℂ) :
    (∑ p ∈ range m, ∑ p' ∈ range m, ∑ q ∈ range m, ∑ q' ∈ range m,
      if ((m-n)*p+q)%m=((m-n)*p'+q')%m then
        z^(((m-n)*p+q)/m)*star (z^(((m-n)*p'+q')/m)) else 0) =
    ∑ r ∈ range m, A m n r z * star (A m n r z) := by
  have hm : 0 < m := by omega
  have h := finite_fiber_gram ((range m) ×ˢ (range m)) (range m)
    (fun x : ℕ × ℕ => ((m-n)*x.1+x.2)%m)
    (fun x : ℕ × ℕ => z^(((m-n)*x.1+x.2)/m))
    (by intro x _; exact mem_range.mpr (Nat.mod_lt _ hm))
  simp only [sum_product, sum_filter] at h
  calc
    _ = ∑ p ∈ range m, ∑ q ∈ range m, ∑ p' ∈ range m, ∑ q' ∈ range m,
        if ((m-n)*p+q)%m=((m-n)*p'+q')%m then
          z^(((m-n)*p+q)/m)*star (z^(((m-n)*p'+q')/m)) else 0 := by
      apply sum_congr rfl
      intro p _
      rw [sum_comm]
    _ = ∑ r ∈ range m,
        (∑ p ∈ range m, ∑ q ∈ range m,
          if ((m-n)*p+q)%m=r then z^(((m-n)*p+q)/m) else 0) *
        star (∑ p ∈ range m, ∑ q ∈ range m,
          if ((m-n)*p+q)%m=r then z^(((m-n)*p+q)/m) else 0) := h
    _ = _ := sum_congr rfl (fun r hr => by rw [fiber_sum_all hmn (mem_range.mp hr) z])

end BergmanUnitCircle
