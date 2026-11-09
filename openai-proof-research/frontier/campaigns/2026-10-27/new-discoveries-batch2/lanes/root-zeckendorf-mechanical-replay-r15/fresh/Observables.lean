import UniformSuffix
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame
attribute [local instance] Classical.propDecidable

def splitBit (m : Move) : ℕ := 1 - combine m
def X (w : List Move) (i : ℕ) : ℕ :=
  if i = 0 then 0 else splitBit ((w[i-1]?).getD .C1)
def splitCount (w : List Move) : ℕ := (w.map splitBit).sum

theorem bit_combine (m : Move) : splitBit m + combine m = 1 := by
  cases m <;> simp [splitBit,combine]

theorem splitCount_add (u v : List Move) :
    splitCount (u++v) = splitCount u + splitCount v := by
  simp [splitCount]

theorem splitCount_combine (w : List Move) :
    splitCount w + (w.map combine).sum = w.length := by
  induction w with
  | nil => simp [splitCount]
  | cons m w ih =>
    have := bit_combine m
    simp only [splitCount,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem X_cons (a : Move) (w : List Move) (i : ℕ) :
    X (a::w) (i+2) = X w (i+1) := by simp [X]

theorem X_one (a : Move) (w : List Move) : X (a::w) 1 = splitBit a := by
  simp [X]

theorem X_nil (i : ℕ) : X [] i = 0 := by simp [X,splitBit,combine]

theorem X_padded (w : List Move) (i : ℕ) (hi : w.length < i) : X w i = 0 := by
  have h : w[i-1]? = none := List.getElem?_eq_none (by omega)
  simp [X,h,splitBit,combine]

theorem sum_X (w : List Move) (m : ℕ) :
    (∑ j ∈ Finset.range m, X w (j+1)) = splitCount (w.take m) := by
  induction m generalizing w with
  | zero => simp [splitCount]
  | succ m ih =>
    cases w with
    | nil => simp [X_nil,splitCount]
    | cons a w =>
      rw [Finset.sum_range_succ']
      simp only [X_cons,X_one,List.take_succ_cons]
      rw [ih]
      simp [splitCount,add_comm,X]

theorem prefix_observable {N : ℕ} {w : List Move}
    (hw : w ∈ completeDomain N) (m : ℕ) :
    w.length < m ↔ N-Z N < m-(∑ j ∈ Finset.range m, X w (j+1)) := by
  obtain ⟨b,he,ht⟩ := (domain_exact N w).mp hw
  have hc := complete_combine_count he ht
  rw [sum_X]
  by_cases hm : w.length < m
  · rw [List.take_of_length_le (by omega)]
    have hs := splitCount_combine w
    omega
  · have hl : (w.take m).length = m := by simp; omega
    have hs := splitCount_combine (w.take m)
    have ha : (w.map combine).sum =
        ((w.take m).map combine).sum + ((w.drop m).map combine).sum := by
      rw [← List.sum_append,← List.map_append,List.take_append_drop]
    omega

theorem X_eq_one (w : List Move) (i : ℕ) :
    X w i = 1 ↔ ∃ u a v, w=u++a::v ∧ i=u.length+1 ∧ IsSplit a := by
  induction w generalizing i with
  | nil => simp [X_nil]
  | cons a w ih =>
    cases i with
    | zero => simp [X]
    | succ i =>
      cases i with
      | zero =>
        change splitBit a = 1 ↔ _
        constructor
        · intro h
          refine ⟨[],a,w,rfl,rfl,?_⟩
          cases a <;> simp_all [splitBit,combine,IsSplit]
        · rintro ⟨u,b,v,h,hu,hb⟩
          have : u=[] := List.length_eq_zero_iff.mp (by omega)
          subst u
          simp only [List.nil_append,List.cons.injEq] at h
          rw [h.1]
          cases b <;> simp_all [splitBit,combine,IsSplit]
      | succ i =>
        rw [X_cons,ih]
        constructor
        · rintro ⟨u,b,v,h,hi,hb⟩
          exact ⟨a::u,b,v,by simp [h],by simp [hi],hb⟩
        · rintro ⟨u,b,v,h,hi,hb⟩
          cases u with
          | nil => simp at hi
          | cons c u =>
            simp only [List.cons_append,List.cons.injEq] at h
            exact ⟨u,b,v,h.2,by simp only [List.length_cons] at hi; omega,hb⟩

theorem suffix_observable (w : List Move) (r : ℕ) (hr : 1≤r) :
    r ≤ lastSplit w ↔ ∃ i, r ≤ i ∧ X w i = 1 := by
  constructor
  · intro h
    obtain ⟨u,a,v,hw,ha,hi⟩ := lastSplit_attained w (by omega)
    exact ⟨lastSplit w,h,(X_eq_one w _).mpr ⟨u,a,v,hw,hi,ha⟩⟩
  · rintro ⟨i,hi,hx⟩
    obtain ⟨u,a,v,rfl,rfl,ha⟩ := (X_eq_one w i).mp hx
    exact hi.trans (split_position_le u v a ha)

noncomputable def duration (N : ℕ) : ℕ :=
  ((completeDomain N).image List.length).sup id

theorem length_le_duration {N : ℕ} {w : List Move} (hw : w ∈ completeDomain N) :
    w.length ≤ duration N := by
  exact Finset.le_sup (f:=id) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)

theorem suffix_observable_finite {N : ℕ} {w : List Move}
    (hw : w ∈ completeDomain N) (r : ℕ) (hr : 1≤r) :
    r ≤ lastSplit w ↔ ∃ i ∈ Finset.Icc r (duration N), X w i=1 := by
  rw [suffix_observable w r hr]
  constructor
  · rintro ⟨i,hi,hx⟩
    have hl : i≤w.length := by
      by_contra hn
      rw [X_padded w i (by omega)] at hx
      omega
    exact ⟨i,Finset.mem_Icc.mpr ⟨hi,hl.trans (length_le_duration hw)⟩,hx⟩
  · rintro ⟨i,hi,hx⟩
    exact ⟨i,(Finset.mem_Icc.mp hi).1,hx⟩

end LiteralGame
