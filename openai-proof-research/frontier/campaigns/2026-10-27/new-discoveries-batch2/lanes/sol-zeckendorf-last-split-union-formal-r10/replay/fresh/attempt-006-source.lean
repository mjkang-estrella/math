import Prefix
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame

theorem compress_append_C2 (u v : List Move) :
    compress (u ++ C2 :: v) = compress u ++ C2 :: compress v := by
  induction u using compress.induct with
  | case1 rest ih => simpa [compress] using congrArg (List.cons C2) ih
  | case2 m rest hn ih =>
    cases rest with
    | nil => cases m <;> simp [compress]
    | cons k rest =>
      cases m <;> cases k <;> simp_all [compress]
  | case3 => simp [compress]

theorem compress_length_mono (u v : List Move) :
    (compress u).length ≤ (compress (u ++ v)).length := by
  induction u using compress.induct with
  | case1 rest ih => simpa [compress] using Nat.succ_le_succ ih
  | case2 m rest hn ih =>
    cases rest with
    | nil =>
      cases v with
      | nil => simp
      | cons k v => cases m <;> cases k <;> simp [compress]
    | cons k rest => cases m <;> cases k <;> simp_all [compress]
  | case3 => simp [compress]

theorem marked_append {a b : Board} {u v : List Move} {i : ℕ}
    (hu : Executes a u b) (hi : i ∈ markedSlots b v) :
    u.length + i ∈ markedSlots a (u ++ v) := by
  induction hu with
  | nil => simpa using hi
  | @cons a mid b m u hs he ih =>
    have hn := step_deterministic (next_step ((mem_legalTypes _ _).mpr ⟨mid,hs⟩)) hs
    have h := (marked_succ a m (u ++ v) (u.length+i)).mpr (hn.symm ▸ ih hi)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem two_C1_twos {a b c : Board} (h1 : Step a .C1 b) (h2 : Step b .C1 c) :
    2 ≤ c.count 2 := by
  obtain ⟨r,ha,hb⟩ := h1
  obtain ⟨s,hb',hc⟩ := h2
  have h := congrArg (Multiset.count 2) (hb.symm.trans hb')
  simp [input,output] at h ⊢
  simp [hc,output]
  omega

-- The index is computed in the globally compressed prefix, so a preceding
-- S2 may consume the first C1 without destroying this C2 or its mark.
theorem successful_triple_mark {a b c d e : Board} {u v : List Move}
    (hu : Executes a u b) (h1 : Step b .C1 c) (h2 : Step c .C1 d)
    (_h3 : Step d C2 e) :
    (compress (u ++ [.C1,.C1])).length ∈
      markedSlots a (compress (u ++ [.C1,.C1,C2] ++ v)) := by
  have hp := executes_append hu (Executes.cons h1 (Executes.cons h2 (Executes.nil _)))
  have hc := compress_executes hp
  have hz : 0 ∈ markedSlots d (C2 :: compress v) :=
    (marked_zero d C2 _).mpr ⟨rfl,two_C1_twos h1 h2⟩
  have hi := marked_append hc hz
  have he : u ++ [.C1,.C1,C2] ++ v = (u ++ [.C1,.C1]) ++ C2 :: v := by
    simp [List.append_assoc]
  rw [he,compress_append_C2]
  simpa using hi

theorem successful_indices_distinct (u gap : List Move) :
    (compress (u ++ [.C1,.C1])).length <
      (compress (u ++ [.C1,.C1,C2] ++ gap ++ [.C1,.C1])).length := by
  have hm := compress_length_mono (u ++ [.C1,.C1,C2]) (gap ++ [.C1,.C1])
  have he : u ++ [.C1,.C1,C2] = (u ++ [.C1,.C1]) ++ [C2] := by
    simp [List.append_assoc]
  rw [he,compress_append_C2] at hm
  simp only [List.length_append,List.length_cons,List.length_nil,compress] at hm
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hm ⊢
  omega
end LiteralGame
