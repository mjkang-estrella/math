import RawIndex
namespace RawIndex
open Delta153
set_option linter.unusedSimpArgs false
 theorem wye_of_row (g : Graph) (x a b c : Fin g.length)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hr : ∀ v : Fin g.length, edge g x.val v.val =
      if v = a ∨ v = b ∨ v = c then 2 else 0) : wye g x.val = true := by
  have hmem (i : Nat) (hi : i ∈ verts g) :
      edge g x.val i ≠ 0 ↔ i = a.val ∨ i = b.val ∨ i = c.val := by
    have := hr ⟨i, List.mem_range.mp hi⟩
    simp only [← Fin.val_inj] at this
    rw [this]
    split_ifs <;> simp_all
  have hs : ((verts g).filter (fun i => edge g x.val i != 0)).toFinset =
      {a.val,b.val,c.val} := by
    ext i
    simp only [List.mem_toFinset, List.mem_filter, bne_iff_ne, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hi,he⟩; exact (hmem i hi).mp he
    · intro hi
      have hm : i ∈ verts g := by
        rcases hi with rfl | rfl | rfl <;> simp [verts]
      exact ⟨hm, (hmem i hm).mpr hi⟩
  have hc : ((verts g).filter (fun i => edge g x.val i != 0)).length = 3 := by
    have hn := (List.nodup_range (n := g.length)).filter (fun i => edge g x.val i != 0)
    change ((verts g).filter (fun i => edge g x.val i != 0)).Nodup at hn
    have ha : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hb : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have hd : b.val ≠ c.val := fun h => hbc (Fin.ext h)
    have := congrArg Finset.card hs
    rw [List.toFinset_card_of_nodup hn] at this
    simpa [ha,hb,hd] using this
  simp only [wye, hc, beq_self_eq_true, Bool.true_and]
  apply List.all_eq_true.mpr
  intro i hi
  have := hr ⟨i,List.mem_range.mp hi⟩
  split_ifs at this <;> simp [this]
end RawIndex
