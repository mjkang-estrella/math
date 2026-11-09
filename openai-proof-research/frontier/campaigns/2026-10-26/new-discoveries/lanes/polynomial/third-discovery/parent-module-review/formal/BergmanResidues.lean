import BergmanFloor

open Finset
namespace BergmanUnitCircle

lemma representative_identity {m n r p : ℕ} (hmn : n < m) (hr : r < m) :
    (m-n)*p+(n*p+r)%m = m*(p-(n*p+r)/m)+r := by
  have hf := floor_le_index hmn hr (p:=p)
  have hd := Nat.mod_add_div (n*p+r) m
  have hsub := Nat.sub_add_cancel hf
  have hk := Nat.sub_add_cancel (le_of_lt hmn)
  nlinarith

lemma representative_mod {m n r p : ℕ} (hmn : n < m) (hr : r < m) :
    ((m-n)*p+(n*p+r)%m)%m = r := by
  rw [representative_identity hmn hr]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

lemma representative_height {m n r p : ℕ} (hmn : n < m) (hr : r < m) :
    ((m-n)*p+(n*p+r)%m)/m = p-(n*p+r)/m := by
  rw [representative_identity hmn hr]
  have hm : 0 < m := by omega
  simpa [Nat.add_comm, Nat.div_eq_of_lt hr] using
    (Nat.add_mul_div_left r (p-(n*p+r)/m) hm)

lemma residue_unique {m n p q q' : ℕ} (hq : q < m) (hq' : q' < m)
    (he : ((m-n)*p+q)%m=((m-n)*p+q')%m) : q=q' := by
  have hmod : (m-n)*p+q ≡ (m-n)*p+q' [MOD m] := he
  exact (Nat.ModEq.add_left_cancel' _ hmod).eq_of_lt_of_lt hq hq'

lemma residue_iff {m n r p q : ℕ} (hmn : n < m) (hr : r < m) (hq : q < m) :
    ((m-n)*p+q)%m=r ↔ q=(n*p+r)%m := by
  have hm : 0 < m := by omega
  constructor
  · intro he
    exact residue_unique hq (Nat.mod_lt _ hm) (he.trans (representative_mod hmn hr).symm)
  · intro he
    rw [he,representative_mod hmn hr]

lemma fiber_sum {m n r p : ℕ} (hmn : n < m) (hr : r < m) (z : ℂ) :
    (∑ q ∈ range m, if ((m-n)*p+q)%m=r then z^(((m-n)*p+q)/m) else 0) =
    z^(p-(n*p+r)/m) := by
  have hm : 0 < m := by omega
  rw [Finset.sum_eq_single ((n*p+r)%m)]
  · rw [representative_mod hmn hr,ite_eq_left rfl,representative_height hmn hr]
  · intro q hqm hne
    rw [ite_eq_right]
    intro he
    exact hne ((residue_iff hmn hr (mem_range.mp hqm)).mp he)
  · intro hnot
    exact (hnot (mem_range.mpr (Nat.mod_lt _ hm))).elim

lemma fiber_sum_all {m n r : ℕ} (hmn : n < m) (hr : r < m) (z : ℂ) :
    (∑ p ∈ range m, ∑ q ∈ range m,
      if ((m-n)*p+q)%m=r then z^(((m-n)*p+q)/m) else 0) = A m n r z := by
  exact Finset.sum_congr rfl (fun p _ => fiber_sum hmn hr z)

end BergmanUnitCircle
