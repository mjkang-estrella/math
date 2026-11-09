import StackSortInj2Glue
namespace StackSort
open BigOperators
/-- Bool records the two ends; both independent choices are retained in the pair. -/
def endInsert (n : ℕ) (b : Bool) (w : List ℕ) : List ℕ :=
  if b then n :: w else w ++ [n]

theorem endInsert_mem {n : ℕ} {w : List ℕ} (hw : w ∈ words n) (b : Bool) :
    endInsert n b w ∈ words (n+1) := by
  apply mem_words.mpr
  have hp := mem_words.mp hw
  rw [List.range_succ]
  cases b with
  | false => exact hp.append_right [n]
  | true => exact (hp.cons n).trans (by simpa using List.perm_append_comm (l₁ := [n]) (l₂ := List.range n))

theorem endInsert_sort {n : ℕ} {w : List ℕ} (hw : w ∈ words n) (b : Bool) :
    s (endInsert n b w) = s w ++ [n] := by
  have hb : ∀ x ∈ w, x < n := fun x hx => List.mem_range.mp ((mem_words.mp hw).mem_iff.mp hx)
  cases b with
  | false => simpa [endInsert, show s [] = [] from rfl] using s_split w [] n hb (by simp)
  | true => simpa [endInsert, show s [] = [] from rfl] using s_split [] w n (by simp) (fun x hx => (hb x hx).le)

theorem endInsert_cross_ne {n : ℕ} (hn : 0 < n) {u v : List ℕ}
    (hv : v ∈ words n) : n :: u ≠ v ++ [n] := by
  intro he
  have hl : v.length = n := by simpa using (mem_words.mp hv).length_eq
  cases v with
  | nil => simp at hl; omega
  | cons x xs =>
    have hx : x < n := List.mem_range.mp ((mem_words.mp hv).mem_iff.mp (by simp))
    have hnx := List.cons.inj he |>.1
    omega

theorem endInsert_injective {n : ℕ} (hn : 0 < n) {u v : List ℕ}
    (hu : u ∈ words n) (hv : v ∈ words n) {b c : Bool}
    (he : endInsert n b u = endInsert n c v) : b = c ∧ u = v := by
  cases b <;> cases c
  · exact ⟨rfl, List.append_cancel_right he⟩
  · exact False.elim (endInsert_cross_ne hn hu he.symm)
  · exact False.elim (endInsert_cross_ne hn hv he)
  · exact ⟨rfl, List.cons.inj he |>.2⟩

/-- All four end families, including the two cross families, are disjoint. -/
theorem four_mul_P_le (n : ℕ) (hn : 0 < n) : 4 * P n ≤ P (n+1) := by
  let pairs := ((words n ×ˢ words n).filter (fun p => s p.1 = s p.2))
  let dom := (Finset.univ : Finset (Bool × Bool)) ×ˢ pairs
  let f := fun p : (Bool × Bool) × (List ℕ × List ℕ) =>
    (endInsert n p.1.1 p.2.1, endInsert n p.1.2 p.2.2)
  have hb : dom.card ≤ P (n+1) := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      obtain ⟨_, hp⟩ := Finset.mem_product.mp hp
      obtain ⟨hpw, hps⟩ := Finset.mem_filter.mp hp
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hpw
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨endInsert_mem hu _, endInsert_mem hv _⟩,
        by dsimp [f]; rw [endInsert_sort hu, endInsert_sort hv, hps]⟩
    · intro p hp q hq he
      obtain ⟨_, hp⟩ := Finset.mem_product.mp hp
      obtain ⟨_, hq⟩ := Finset.mem_product.mp hq
      have hpw := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hqw := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      have h1 := endInsert_injective hn hpw.1 hqw.1 (congrArg Prod.fst he)
      have h2 := endInsert_injective hn hpw.2 hqw.2 (congrArg Prod.snd he)
      exact Prod.ext (Prod.ext h1.1 h2.1) (Prod.ext h1.2 h2.2)
  simpa [dom, pairs, Finset.card_product, P] using hb
end StackSort
