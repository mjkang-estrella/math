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
      by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> simp_all [input]
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
  · refine ⟨t+{1},?_,?_⟩ <;> apply Multiset.ext.mpr <;> intro i <;> simp [input,output,Multiset.count_cons,Multiset.count_singleton] <;> omega
  constructor
  · refine ⟨t+{3},?_,?_⟩ <;> apply Multiset.ext.mpr <;> intro i <;> simp [input,output,Multiset.count_cons,Multiset.count_singleton,add_comm]
  · refine ⟨t+{2},?_,?_⟩ <;> apply Multiset.ext.mpr <;> intro i <;> simp [input,output,Multiset.count_cons,Multiset.count_singleton] <;> omega

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
  simp [input,Multiset.count_cons,Multiset.count_singleton]
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

theorem compress_head (ms : List Move) (rest : List Move)
    (h : compress ms = .C1 :: rest) : ∃ tail, ms = .C1 :: tail := by
  induction ms using compress.induct with
  | case1 tail ih => simp [compress] at h
  | case2 m tail hn ih =>
    have hh : m :: compress tail = .C1 :: rest := by simpa [compress,hn] using h
    exact ⟨tail,congrArg (fun x => x :: tail) (List.cons.inj hh).1⟩
  | case3 => simp [compress] at h

theorem compress_reduced (ms : List Move) : Reduced (compress ms) := by
  induction ms using compress.induct with
  | case1 rest ih => simpa [compress,Reduced] using ih
  | case2 m rest hn ih =>
    simp only [compress,hn]
    cases m with
    | C1 => simpa [Reduced] using ih
    | Ck k => simpa [Reduced] using ih
    | Sk k => simpa [Reduced] using ih
    | S2 =>
      cases hr : compress rest with
      | nil => trivial
      | cons head tail =>
        cases head with
        | C1 =>
          obtain ⟨r,he⟩ := compress_head rest tail hr
          exact (hn r rfl he).elim
        | Ck k => simpa [Reduced,hr] using ih
        | Sk k => simpa [Reduced,hr] using ih
        | S2 => simpa [Reduced,hr] using ih
  | case3 => trivial

theorem compress_fixed {ms : List Move} (h : Reduced ms) : compress ms = ms := by
  induction ms using compress.induct with
  | case1 rest ih => exact h.elim
  | case2 m rest hn ih =>
    have ht : Reduced rest := by
      cases m <;> cases rest <;> simp_all [Reduced]
    simpa [compress] using congrArg (List.cons m) (ih ht)
  | case3 => rfl

theorem compress_idempotent (ms : List Move) : compress (compress ms) = compress ms :=
  compress_fixed (compress_reduced ms)

def cell (N : ℕ) (R : List Move) : Set (List Move) :=
  {ms | ms ∈ completeWords N ∧ compress ms = R}

theorem exhaustive_cells (N : ℕ) (ms : List Move) (h : ms ∈ completeWords N) :
    ∃! R, R ∈ completeWords N ∧ Reduced R ∧ ms ∈ cell N R := by
  refine ⟨compress ms,⟨compress_complete h,compress_reduced ms,h,rfl⟩,?_⟩
  intro R hR
  exact hR.2.2.2.symm

theorem cells_disjoint {N : ℕ} {R Q : List Move} (h : R ≠ Q) :
    Disjoint (cell N R) (cell N Q) := by
  apply Set.disjoint_left.mpr
  intro ms hr hq
  exact h (hr.2.symm.trans hq.2)

theorem pair_product {a b c : Board} (hs : Step a .S2 b) (hc : Step b .C1 c)
    (rest : List Move) :
    reciprocalProduct a (.S2 :: .C1 :: rest) =
      reciprocalProduct a (C2 :: rest) * ((legalTypes b).card : ℚ)⁻¹ := by
  classical
  have hd := diamond_compress hs hc
  have hS := (mem_legalTypes a .S2).mpr ⟨b,hs⟩
  have hC := (mem_legalTypes b .C1).mpr ⟨c,hc⟩
  have hD := (mem_legalTypes a C2).mpr ⟨c,hd⟩
  have nS := step_deterministic (next_step hS) hs
  have nC := step_deterministic (next_step hC) hc
  have nD := step_deterministic (next_step hD) hd
  simp only [reciprocalProduct,ite_eq_left hS,nS,ite_eq_left hC,nC,
    ite_eq_left hD,nD]
  ring

theorem reciprocal_append (a : Board) (pre rest : List Move) :
    reciprocalProduct a (pre ++ rest) = reciprocalProduct a pre *
      reciprocalProduct (pre.foldl next a) rest := by
  classical
  induction pre generalizing a with
  | nil => simp [reciprocalProduct]
  | cons m pre ih =>
    by_cases hm : m ∈ legalTypes a
    · simp [reciprocalProduct,hm,ih,mul_assoc]
    · simp [reciprocalProduct,hm]

theorem executes_fold {a c : Board} {ms : List Move} (he : Executes a ms c) :
    ms.foldl next a = c := by
  induction he with
  | nil => rfl
  | cons hs hr ih =>
    have hm := (mem_legalTypes _ _).mpr ⟨_,hs⟩
    have hn := step_deterministic (next_step hm) hs
    simpa [hn] using ih

theorem actual_local_weight {N : ℕ} {a b c : Board} {pre rest : List Move}
    (hp : Executes (initial N) pre a) (hs : Step a .S2 b) (hc : Step b .C1 c)
    (hE : pre ++ .S2 :: .C1 :: rest ∈ completeWords N)
    (hR : pre ++ C2 :: rest ∈ completeWords N) :
    P N (pre ++ .S2 :: .C1 :: rest) =
      P N (pre ++ C2 :: rest) * ((legalTypes b).card : ℚ)⁻¹ := by
  rw [P_product N hE,P_product N hR,reciprocal_append,reciprocal_append,
    executes_fold hp,pair_product hs hc]
  ring

-- Slots are indexed in the SHORT word; every test uses its pre-move board.
noncomputable def markedSlots : Board → List Move → Finset ℕ
  | _, [] => ∅
  | a, m :: rest => by
    classical
    exact (if m = C2 ∧ 2 ≤ a.count 2 then {0} else ∅) ∪
      (markedSlots (next a m) rest).image Nat.succ

inductive Expansion : Board → List Move → List Move → Board → Prop
  | nil (a : Board) : Expansion a [] [] a
  | keep {a b c : Board} {m : Move} {R G : List Move} :
      Step a m b → Expansion b R G c → Expansion a (m::R) (m::G) c
  | split {a b d c : Board} {R G : List Move} :
      Step a .S2 b → Step b .C1 d → Expansion d R G c →
      Expansion a (C2::R) (.S2::.C1::G) c

theorem expansion_short_executes {a c : Board} {R G : List Move}
    (h : Expansion a R G c) : Executes a R c := by
  induction h with
  | nil => exact Executes.nil _
  | keep hs _ ih => exact Executes.cons hs ih
  | split hs hc _ ih => exact Executes.cons (diamond_compress hs hc) ih

theorem expansion_long_executes {a c : Board} {R G : List Move}
    (h : Expansion a R G c) : Executes a G c := by
  induction h with
  | nil => exact Executes.nil _
  | keep hs _ ih => exact Executes.cons hs ih
  | split hs hc _ ih => exact Executes.cons hs (Executes.cons hc ih)

theorem compression_is_expansion {a c : Board} {G : List Move}
    (he : Executes a G c) : Expansion a (compress G) G c := by
  induction G using compress.induct generalizing a with
  | case1 rest ih =>
    cases he with
    | cons hs ht =>
      cases ht with
      | cons hc hr => exact Expansion.split hs hc (ih hr)
  | case2 m rest hn ih =>
    cases he with
    | cons hs hr => simpa [compress,hn] using Expansion.keep hs (ih hr)
  | case3 => cases he; exact Expansion.nil _

theorem expansion_head {a c : Board} {R G tail : List Move}
    (h : Expansion a R G c) (he : G = .C1 :: tail) :
    ∃ rest, R = .C1 :: rest := by
  cases h with
  | nil => simp at he
  | keep hs ht => exact ⟨_,congrArg (fun m => m :: _) (List.cons.inj he).1⟩
  | split hs hc ht => simp at he

theorem expansion_compress {a c : Board} {R G : List Move}
    (h : Expansion a R G c) (hr : Reduced R) : compress G = R := by
  induction h with
  | nil => rfl
  | @keep a b c m R G hs ht ih =>
    have htail : Reduced R := by cases m <;> cases R <;> simp_all [Reduced]
    have hn : ∀ rest, m = .S2 → G = .C1 :: rest → False := by
      intro rest hm hg
      subst m
      obtain ⟨tail,he⟩ := expansion_head ht hg
      simp [he,Reduced] at hr
    simpa [compress,hn] using congrArg (List.cons m) (ih htail)
  | split hs hc ht ih => simpa [compress] using congrArg (List.cons C2) (ih hr)

theorem cell_iff_expansion {N : ℕ} {R G : List Move} (hr : Reduced R) :
    G ∈ cell N R ↔ ∃ c, Expansion (initial N) R G c ∧ Terminal c := by
  constructor
  · rintro ⟨⟨c,he,hc⟩,hR⟩
    exact ⟨c,hR ▸ compression_is_expansion he,hc⟩
  · rintro ⟨c,he,hc⟩
    exact ⟨⟨c,expansion_long_executes he,hc⟩,expansion_compress he hr⟩

end LiteralGame
