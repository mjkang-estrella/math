import StackSortSeeds2Tuples
namespace StackSort.Seeds2

 theorem output_append (A B : List (List ℕ)) : output (A ++ B) = output A ++ output B := by
  simp [output]

 theorem output_perm (F : List (List ℕ)) : (output F).Perm F.flatten := by
  induction F with
  | nil => exact List.Perm.refl []
  | cons w F ih => simpa [output] using (s_perm w).append ih

 theorem maximum_terminal (w : List ℕ) (m : ℕ) (hm : m ∈ w)
    (hb : ∀ x ∈ w, x ≤ m) : ∃ v, s w = v ++ [m] := by
  let L := w.takeWhile (· != m)
  let R := (w.dropWhile (· != m)).drop 1
  have he : w = L ++ m :: R := split_spec w m hm
  have hL : ∀ x ∈ L, x < m := by
    intro x hx
    have hxw : x ∈ w := by rw [he]; simp [hx]
    have hn : x ≠ m := by
      have hh := List.all_eq_true.mp (List.all_takeWhile (p := fun x => x != m) (l := w)) x hx
      simpa using hh
    exact lt_of_le_of_ne (hb x hxw) hn
  have hR : ∀ x ∈ R, x ≤ m := by
    intro x hx
    apply hb x
    rw [he]; simp [hx]
  refine ⟨s L ++ s R, ?_⟩
  rw [he, s_split L R m hL hR]

/-- A boundary is measured in output positions, including the two exterior boundaries. -/
def Boundary (F : List (List ℕ)) (k : ℕ) : Prop :=
  ∃ A B, F = A ++ B ∧ (output A).length = k

def Irreducible (F G : List (List ℕ)) : Prop :=
  ∀ k, Boundary F k → Boundary G k → 0 < k → k < (output F).length → False

 theorem maximum_boundary (F : List (List ℕ)) (m : ℕ)
    (hn : F.flatten.Nodup) (hm : m ∈ F.flatten)
    (hb : ∀ x ∈ F.flatten, x ≤ m) :
    Boundary F ((output F).idxOf m + 1) := by
  obtain ⟨w, hw, hmw⟩ := List.mem_flatten.mp hm
  obtain ⟨A, B, hF⟩ := List.append_of_mem hw
  obtain ⟨v, hv⟩ := maximum_terminal w m hmw (fun x hx => hb x (List.mem_flatten.mpr ⟨w, hw, hx⟩))
  have hout : output F = (output A ++ v) ++ m :: output B := by
    rw [hF, output_append]
    simp [output, hv, List.append_assoc]
  have hnod : ((output A ++ v) ++ m :: output B).Nodup :=
    hout ▸ ((output_perm F).nodup_iff.mpr hn)
  have hnot : m ∉ output A ++ v := by
    intro hm'
    exact (List.nodup_append.mp hnod).2.2 m hm' m (by simp) rfl
  refine ⟨A ++ [w], B, by simpa [List.append_assoc] using hF, ?_⟩
  rw [hout, List.idxOf_append]
  simp only [hnot, List.idxOf_cons_self, Nat.zero_add]
  rw [output_append]
  simp [output, hv, List.length_append, Nat.add_assoc]

/-- T2: in an irreducible collision, the common maximum occupies the final output position. -/
 theorem irreducible_maximum_last (F G : List (List ℕ)) (m : ℕ)
    (hnF : F.flatten.Nodup) (hnG : G.flatten.Nodup)
    (hmF : m ∈ F.flatten) (hmG : m ∈ G.flatten)
    (hbF : ∀ x ∈ F.flatten, x ≤ m) (hbG : ∀ x ∈ G.flatten, x ≤ m)
    (he : output F = output G) (hi : Irreducible F G) :
    (output F).idxOf m + 1 = (output F).length := by
  have hF := maximum_boundary F m hnF hmF hbF
  have hG := maximum_boundary G m hnG hmG hbG
  rw [← he] at hG
  have hm : m ∈ output F := (output_perm F).mem_iff.mpr hmF
  have hlt := List.idxOf_lt_length_of_mem hm
  by_contra hne
  exact hi _ hF hG (by omega) (by omega)

end StackSort.Seeds2
