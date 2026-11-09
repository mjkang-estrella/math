import Law
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame

abbrev C2 : Move := .Ck 0
def Expandable (a : Board) : Prop := ∃ t, a = t + {1,2,2}

theorem expandable_iff (a : Board) : Expandable a ↔
    (∃ c, Step a C2 c) ∧ 2 ≤ a.count 2 := by
  rw [has_step_iff]
  constructor
  · rintro ⟨t,rfl⟩
    constructor
    · apply Multiset.le_iff_count.mpr
      intro i
      by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> simp_all [input] <;> omega
    · simp
  · rintro ⟨hc,h2⟩
    have h1 := Multiset.le_iff_count.mp hc 1
    have ht : ({1,2,2} : Board) ≤ a := by
      apply Multiset.le_iff_count.mpr
      intro i
      by_cases e1 : i=1
      · subst i; simpa [input] using h1
      by_cases e2 : i=2
      · subst i; simpa using h2
      simp [e1,e2]
    obtain ⟨t,ht⟩ := Multiset.le_iff_exists_add.mp ht
    exact ⟨t,by simpa [add_comm] using ht⟩

theorem diamond_steps (t : Board) :
    Step (t+{1,2,2}) .S2 (t+{1,1,3}) ∧
    Step (t+{1,1,3}) .C1 (t+{2,3}) ∧
    Step (t+{1,2,2}) C2 (t+{2,3}) := by
  constructor
  · refine ⟨t+{1},?_,?_⟩ <;> apply Multiset.ext.mpr <;> intro i <;> simp [input,output] <;> omega
  constructor
  · refine ⟨t+{3},?_,?_⟩ <;> apply Multiset.ext.mpr <;> intro i <;> simp [input,output] <;> omega
  · refine ⟨t+{2},?_,?_⟩ <;> apply Multiset.ext.mpr <;> intro i <;> simp [input,output] <;> omega

theorem pair_expandable {a b c : Board}
    (hs : Step a .S2 b) (hc : Step b .C1 c) : Expandable a := by
  obtain ⟨r,ha,hb⟩ := hs
  have h1 := Multiset.le_iff_count.mp ((has_step_iff b .C1).mp ⟨c,hc⟩) 1
  have hr : ({1} : Board) ≤ r := by
    apply Multiset.le_iff_count.mpr
    intro i
    by_cases hi : i=1
    · subst i; simp [hb,input,output] at h1 ⊢; omega
    · simp [hi]
  obtain ⟨t,ht⟩ := Multiset.le_iff_exists_add.mp hr
  refine ⟨t,?_⟩
  rw [ha,ht]
  apply Multiset.ext.mpr
  intro i
  simp [input]
  omega

theorem diamond_compress {a b c : Board}
    (hs : Step a .S2 b) (hc : Step b .C1 c) : Step a C2 c := by
  obtain ⟨t,ha⟩ := pair_expandable hs hc
  subst a
  obtain ⟨hs',hc',hd⟩ := diamond_steps t
  have hb := step_deterministic hs hs'
  subst b
  have he := step_deterministic hc hc'
  subst c
  exact hd

theorem diamond_expand {a c : Board} (hd : Step a C2 c)
    (h2 : 2 ≤ a.count 2) : ∃ b, Step a .S2 b ∧ Step b .C1 c := by
  obtain ⟨t,ha⟩ := (expandable_iff a).mpr ⟨⟨c,hd⟩,h2⟩
  subst a
  obtain ⟨hs,hc,hd'⟩ := diamond_steps t
  have he := step_deterministic hd hd'
  subst c
  exact ⟨_,hs,hc⟩

def compress : List Move → List Move
  | .S2 :: .C1 :: rest => C2 :: compress rest
  | m :: rest => m :: compress rest
  | [] => []

def Reduced : List Move → Prop
  | .S2 :: .C1 :: _ => False
  | _ :: rest => Reduced rest
  | [] => True

theorem compress_executes {a c : Board} {ms : List Move}
    (he : Executes a ms c) : Executes a (compress ms) c := by
  induction ms using compress.induct generalizing a with
  | case1 rest ih =>
    cases he with
    | cons hs ht =>
      cases ht with
      | cons hc hr => exact Executes.cons (diamond_compress hs hc) (ih hr)
  | case2 m rest hn ih =>
    cases he with
    | cons hs hr => simpa [compress,hn] using Executes.cons hs (ih hr)
  | case3 => exact he

theorem compress_complete {N : ℕ} {ms : List Move}
    (h : ms ∈ completeWords N) : compress ms ∈ completeWords N := by
  obtain ⟨c,he,hc⟩ := h
  exact ⟨c,compress_executes he,hc⟩

end LiteralGame
