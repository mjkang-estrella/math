import Concrete
namespace ChainPrefix
open Literal
set_option linter.unusedSimpArgs false
abbrev V := Fin 11
abbrev Es := List (Edge Concrete.g7.order)
def tri (a b c : V) : Es := [(a,b),(a,c),(b,c)]
def dbl (a b : V) : Es := [(a,b),(a,b)]
def Fits (es : Es) : Prop := ∀ i j, pairCount es i j ≤ Concrete.g7.edge i j
def fastFits (es : Es) : Bool := es.all fun e => decide (pairCount es e.1 e.2 ≤ Concrete.g7.edge e.1 e.2)

theorem pairCount_symm {n} (es : List (Edge n)) (i j : Fin n) :
    pairCount es i j = pairCount es j i := by
  simp only [pairCount, or_comm]

theorem fastFits_iff (es : Es) : fastFits es = true ↔ Fits es := by
  constructor
  · intro hf i j
    by_cases hz : pairCount es i j = 0
    · simp [hz]
    · have hp : 0 < (es.filter (fun e => (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i))).length := Nat.pos_of_ne_zero hz
      obtain ⟨e,he⟩ := List.length_pos_iff_exists_mem.mp hp
      obtain ⟨hm,hp⟩ := List.mem_filter.mp he
      have hb := of_decide_eq_true (List.all_eq_true.mp hf e hm)
      simp only [decide_eq_true_eq] at hp
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hb
      · simpa only [pairCount_symm es e.2 e.1, Concrete.g7.symm e.2 e.1] using hb
  · intro hf
    exact List.all_eq_true.mpr (fun e _ => decide_eq_true (hf e.1 e.2))

instance (es : Es) : Decidable (Fits es) := decidable_of_iff (fastFits es = true) (fastFits_iff es)
def first (a b c l m : V) : Es := tri a b c ++ dbl a l ++ dbl a m

theorem end_options : ∀ v : V, EndVertex Concrete.g7 v → v = 3 ∨ v = 6 := by
  unfold EndVertex Concrete.g7
  decide +kernel

theorem count_mono {n} {xs ys : List (Edge n)} (h : xs.Sublist ys) (i j : Fin n) :
    pairCount xs i j ≤ pairCount ys i j := by
  exact (h.filter _).length_le

theorem fits_sublist {xs ys : Es} (h : xs.Sublist ys) (hy : Fits ys) : Fits xs := by
  intro i j
  exact (count_mono h i j).trans (hy i j)
@[simp] theorem pairCount_nil {n} (i j : Fin n) : pairCount ([] : List (Edge n)) i j = 0 := rfl
theorem pairCount_cons {n} (e : Edge n) (es : List (Edge n)) (i j : Fin n) :
    pairCount (e::es) i j = (if (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i) then 1 else 0) + pairCount es i j := by
  unfold pairCount
  split_ifs <;> simp_all [Nat.add_comm]
theorem pairCount_append {n} (xs ys : List (Edge n)) (i j : Fin n) :
    pairCount (xs ++ ys) i j = pairCount xs i j + pairCount ys i j := by
  simp [pairCount, List.filter_append]

theorem chain0_first (ch : Chain Concrete.g7 0) :
    Fits (first (ch.base 0) (ch.base 1) (ch.apex 0) (ch.left 0) (ch.left 1)) := by
  intro i j
  have h := ch.capacity i j
  simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, pairCount_append] at h
  simp only [first, tri, dbl, pairCount_append]
  simp only [pairCount_cons, pairCount_nil] at h ⊢
  norm_num at h ⊢
  omega
theorem chain1_prefix (ch : Chain Concrete.g7 1) :
    Fits (first (ch.base 0) (ch.base 1) (ch.apex 0) (ch.left 0) (ch.left 1) ++
      dbl (ch.base 1) (ch.attach 0) ++ tri (ch.base 1) (ch.base 2) (ch.apex 1) ++
      dbl (ch.base 2) (ch.right 0)) := by
  intro i j
  have h := ch.capacity i j
  simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, pairCount_append] at h
  simp only [first, tri, dbl, pairCount_append]
  simp only [pairCount_cons, pairCount_nil] at h ⊢
  norm_num [Fin.last] at h ⊢
  omega

theorem chain_long_prefix {k} (ch : Chain Concrete.g7 (k+2)) :
    Fits (first (ch.base 0) (ch.base 1) (ch.apex 0) (ch.left 0) (ch.left 1) ++
      dbl (ch.base 1) (ch.attach 0) ++ tri (ch.base 1) (ch.base 2) (ch.apex 1) ++
      dbl (ch.base 2) (ch.attach 1)) := by
  have hc := Fintype.card_le_of_injective ch.base ch.base_injective
  have hk : k ≤ 7 := by
    simp only [Fintype.card_fin] at hc
    change k+2+2 ≤ 11 at hc
    omega
  interval_cases k <;> intro i j
  all_goals
    have h := ch.capacity i j
    simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, pairCount_append] at h
    simp only [first, tri, dbl, pairCount_append]
    simp only [pairCount_cons, pairCount_nil] at h ⊢
    norm_num [Fin.last] at h ⊢
    omega
end ChainPrefix
