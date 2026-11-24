# Lean source appendix

Complete formalization of both conjuncts of Conjecture 31. All modules have local compile and standalone kernel-check receipts.

### `Geometry.lean`

```lean
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.FinRange

set_option maxHeartbeats 0
namespace Pool039

structure Arc where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq

def Cross (a b : Arc) : Prop :=
  (a.lo < b.lo ∧ b.lo < a.hi ∧ a.hi < b.hi) ∨
  (b.lo < a.lo ∧ a.lo < b.hi ∧ b.hi < a.hi)

def Nest (a b : Arc) : Prop :=
  (a.lo < b.lo ∧ b.hi < a.hi) ∨ (b.lo < a.lo ∧ a.hi < b.hi)

def Separated (a b : Arc) : Prop := a.hi < b.lo ∨ b.hi < a.lo

def Apart (a b : Arc) : Prop :=
  a.lo ≠ b.lo ∧ a.lo ≠ b.hi ∧ a.hi ≠ b.lo ∧ a.hi ≠ b.hi

def ForceS (a b c : Arc) : Prop := Nest a b ∧ Nest a c ∧ Cross b c

def ForceQ (a b c : Arc) : Prop := Cross a b ∧ Cross a c ∧ Nest b c

theorem cross_symm {a b : Arc} (h : Cross a b) : Cross b a := by
  exact h.symm

theorem nest_symm {a b : Arc} (h : Nest a b) : Nest b a := by
  exact h.symm

theorem trichotomy {a b : Arc}
    (ha : a.lo < a.hi) (hb : b.lo < b.hi) (hab : Apart a b) :
    Cross a b ∨ Nest a b ∨ Separated a b := by
  simp only [Cross, Nest, Separated, Apart] at *
  omega

theorem triple_free_extreme {a b c : Arc}
    (ha : a.lo < a.hi) (hb : b.lo < b.hi) (hc : c.lo < c.hi)
    (hab : a.hi < b.hi) (hac : a.hi < c.hi) (hbc : Apart b c)
    (hC : Cross a b) (hN : Nest a c) :
    ForceQ b a c ∨ ForceS c a b := by
  have hn : ¬ Separated b c := by
    simp only [Cross, Nest, Separated] at *
    omega
  rcases trichotomy hb hc hbc with h | h | h
  · exact Or.inl ⟨cross_symm hC, h, hN⟩
  · exact Or.inr ⟨nest_symm hN, nest_symm h, hC⟩
  · exact (hn h).elim

/-- The new path-shortening step; no size bound on an ambient matching. -/
theorem alternating_three {a b c d : Arc}
    (ha : a.lo < a.hi) (hb : b.lo < b.hi)
    (hc : c.lo < c.hi) (hd : d.lo < d.hi)
    (hac : Apart a c) (hbd : Apart b d)
    (hab : Cross a b) (hbc : Nest b c) (hcd : Cross c d) :
    ForceQ a b c ∨ ForceS b c d ∨ ForceS c a b ∨ ForceQ d b c := by
  rcases trichotomy ha hc hac with h | h | h
  · exact Or.inl ⟨hab, h, hbc⟩
  · exact Or.inr (Or.inr (Or.inl ⟨nest_symm h, nest_symm hbc, hab⟩))
  · have hinside : b.lo < c.lo ∧ c.hi < b.hi := by
      simp only [Cross, Nest, Separated] at *
      omega
    have hn : ¬ Separated b d := by
      simp only [Separated, Cross] at *
      omega
    rcases trichotomy hb hd hbd with h' | h' | h'
    · exact Or.inr (Or.inr (Or.inr ⟨cross_symm h', cross_symm hcd, hbc⟩))
    · exact Or.inr (Or.inl ⟨hbc, h', hcd⟩)
    · exact (hn h').elim

/-- A seed forcing Q inside another interval either forces that container S,
or exposes two nested Q seeds. This tightens the obstruction bound to six. -/
theorem contained_Q_seed {a b u v : Arc}
    (ha : a.lo < a.hi) (hb : b.lo < b.hi)
    (hu : u.lo < u.hi) (hv : v.lo < v.hi)
    (hbu : Apart b u) (hbv : Apart b v)
    (hba : b.lo < a.lo ∧ a.hi < b.hi) (h : ForceQ a u v) :
    ForceS b a u ∨ ForceS b a v ∨ (ForceQ u a b ∧ ForceQ v a b) := by
  have hab : Nest a b := Or.inr hba
  have hnu : ¬ Separated b u := by
    have h' := h.1
    simp only [Separated, Cross] at *
    omega
  have hnv : ¬ Separated b v := by
    have h' := h.2.1
    simp only [Separated, Cross] at *
    omega
  rcases trichotomy hb hu hbu with hU | hU | hU
  · rcases trichotomy hb hv hbv with hV | hV | hV
    · exact Or.inr (Or.inr ⟨⟨cross_symm h.1, cross_symm hU, hab⟩,
        ⟨cross_symm h.2.1, cross_symm hV, hab⟩⟩)
    · exact Or.inr (Or.inl ⟨Or.inl hba, hV, h.2.1⟩)
    · exact (hnv hV).elim
  · exact Or.inl ⟨Or.inl hba, hU, h.1⟩
  · exact (hnu hU).elim

theorem cross_nest_separated_contains {a b c : Arc}
    (ha : a.lo < a.hi) (hb : b.lo < b.hi) (_hc : c.lo < c.hi)
    (hab : Cross a b) (hbc : Nest b c) (hac : Separated a c) :
    b.lo < c.lo ∧ c.hi < b.hi := by
  simp only [Cross, Nest, Separated] at *
  omega

theorem cross_not_nest {a b : Arc} (h : Cross a b) : ¬ Nest a b := by
  simp only [Cross, Nest] at *
  omega

theorem cross_irrefl (a : Arc) : ¬ Cross a a := by
  simp only [Cross]; omega

theorem nest_irrefl (a : Arc) : ¬ Nest a a := by
  simp only [Nest]; omega

instance (a b : Arc) : Decidable (Cross a b) := by unfold Cross; infer_instance
instance (a b : Arc) : Decidable (Nest a b) := by unfold Nest; infer_instance

def HasSQ (E : List Arc) : Prop :=
  ∃ q : Fin E.length → Bool, ∀ i j : Fin E.length,
    (q i = false → q j = false → ¬ Cross E[i] E[j]) ∧
    (q i = true → q j = true → ¬ Nest E[i] E[j])

instance (E : List Arc) : Decidable (HasSQ E) := by unfold HasSQ; infer_instance

def OnePage (E : List Arc) : Prop :=
  (∀ i j : Fin E.length, ¬ Cross E[i] E[j]) ∨
  (∀ i j : Fin E.length, ¬ Nest E[i] E[j])

instance (E : List Arc) : Decidable (OnePage E) := by unfold OnePage; infer_instance

def sourceSQ : List (List Arc) := [
  [⟨0, 5⟩, ⟨1, 4⟩, ⟨2, 7⟩, ⟨3, 6⟩],
  [⟨0, 7⟩, ⟨1, 4⟩, ⟨2, 9⟩, ⟨3, 6⟩, ⟨5, 8⟩],
  [⟨0, 6⟩, ⟨1, 7⟩, ⟨2, 4⟩, ⟨3, 5⟩],
  [⟨0, 6⟩, ⟨1, 3⟩, ⟨2, 4⟩, ⟨5, 11⟩, ⟨7, 9⟩, ⟨8, 10⟩],
  [⟨0, 6⟩, ⟨1, 3⟩, ⟨2, 9⟩, ⟨4, 7⟩, ⟨5, 8⟩],
  [⟨0, 7⟩, ⟨1, 4⟩, ⟨2, 5⟩, ⟨3, 9⟩, ⟨6, 8⟩],
  [⟨0, 7⟩, ⟨1, 4⟩, ⟨2, 9⟩, ⟨3, 5⟩, ⟨6, 8⟩],
  [⟨0, 7⟩, ⟨1, 3⟩, ⟨2, 9⟩, ⟨4, 6⟩, ⟨5, 8⟩],
  [⟨0, 5⟩, ⟨1, 3⟩, ⟨2, 9⟩, ⟨4, 7⟩, ⟨6, 8⟩],
  [⟨0, 7⟩, ⟨1, 3⟩, ⟨2, 5⟩, ⟨4, 9⟩, ⟨6, 8⟩],
  [⟨0, 7⟩, ⟨1, 3⟩, ⟨2, 4⟩, ⟨5, 9⟩, ⟨6, 8⟩],
  [⟨0, 4⟩, ⟨1, 3⟩, ⟨2, 9⟩, ⟨5, 7⟩, ⟨6, 8⟩]
]

def sourceOne : List (List Arc) := [
  [⟨0, 4⟩, ⟨1, 3⟩, ⟨2, 5⟩],
  [⟨0, 2⟩, ⟨1, 5⟩, ⟨3, 4⟩],
  [⟨0, 5⟩, ⟨1, 3⟩, ⟨2, 4⟩],
  [⟨0, 2⟩, ⟨1, 3⟩, ⟨4, 7⟩, ⟨5, 6⟩],
  [⟨0, 3⟩, ⟨1, 5⟩, ⟨2, 4⟩],
  [⟨0, 4⟩, ⟨1, 2⟩, ⟨3, 5⟩],
  [⟨0, 4⟩, ⟨1, 5⟩, ⟨2, 3⟩],
  [⟨0, 3⟩, ⟨1, 2⟩, ⟨4, 6⟩, ⟨5, 7⟩]
]

#print axioms alternating_three
#print axioms triple_free_extreme
#print axioms contained_Q_seed
end Pool039
```

### `Criterion.lean`

```lean
import Geometry
set_option maxHeartbeats 0
namespace Pool039

structure OrderedMatching (ι : Type) where
  arc : ι → Arc
  proper : ∀ i, (arc i).lo < (arc i).hi
  apart : ∀ i j, i ≠ j → Apart (arc i) (arc j)

namespace OrderedMatching
variable {ι : Type} (M : OrderedMatching ι)
def C (a b : ι) := Cross (M.arc a) (M.arc b)
def N (a b : ι) := Nest (M.arc a) (M.arc b)
def A (a : ι) := ∃ u v, ForceS (M.arc a) (M.arc u) (M.arc v)
def B (a : ι) := ∃ u v, ForceQ (M.arc a) (M.arc u) (M.arc v)
def LocalGood : Prop :=
 (∀ a, M.A a → ¬ M.B a) ∧
 (∀ a b, M.A a → M.A b → ¬ M.C a b) ∧
 (∀ a b, M.B a → M.B b → ¬ M.N a b)
def Q (a : ι) := M.B a ∨ ∃ s, M.A s ∧ M.C s a
def S (a : ι) := M.A a ∨ ∃ q, M.Q q ∧ M.N q a

theorem Csym {a b : ι} (h : M.C a b) : M.C b a := cross_symm h
theorem Nsym {a b : ι} (h : M.N a b) : M.N b a := nest_symm h

theorem ACN {a b c : ι} (hab : M.C a b) (hbc : M.N b c) : a ≠ c := by
  intro he; subst c
  exact cross_not_nest hab (M.Nsym hbc)

theorem CNC {a b c d : ι} (hab : M.C a b) (hbc : M.N b c) (hcd : M.C c d) :
    M.B a ∨ M.A b ∨ M.A c ∨ M.B d := by
  have hac := M.ACN hab hbc
  have hbd : b ≠ d := by
    intro he; subst d
    exact cross_not_nest (M.Csym hcd) hbc
  rcases alternating_three (M.proper a) (M.proper b) (M.proper c) (M.proper d)
    (M.apart a c hac) (M.apart b d hbd) hab hbc hcd with h | h | h | h
  · exact Or.inl ⟨b,c,h⟩
  · exact Or.inr (Or.inl ⟨c,d,h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a,b,h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨b,c,h⟩))

theorem container {a b : ι} (hg : M.LocalGood) (hB : M.B a)
    (hin : (M.arc b).lo < (M.arc a).lo ∧ (M.arc a).hi < (M.arc b).hi) : M.A b := by
  obtain ⟨u,v,h⟩ := hB
  have hn : Nest (M.arc a) (M.arc b) := Or.inr hin
  have hbu : b ≠ u := by
    intro he; subst u
    exact cross_not_nest h.1 hn
  have hbv : b ≠ v := by
    intro he; subst v
    exact cross_not_nest h.2.1 hn
  rcases contained_Q_seed (M.proper a) (M.proper b) (M.proper u) (M.proper v)
    (M.apart b u hbu) (M.apart b v hbv) hin h with h' | h' | h'
  · exact ⟨a,u,h'⟩
  · exact ⟨a,v,h'⟩
  · exact (hg.2.2 u v ⟨a,b,h'.1⟩ ⟨a,b,h'.2⟩ h.2.2).elim

theorem no_two_link {a b c : ι} (hg : M.LocalGood)
    (hA : M.A a) (hab : M.C a b) (hbc : M.N b c) (hB : M.B c) : False := by
  rcases trichotomy (M.proper a) (M.proper c) (M.apart a c (M.ACN hab hbc)) with h | h | h
  · exact hg.1 a hA ⟨b,c,hab,h,hbc⟩
  · exact hg.1 c ⟨a,b,nest_symm h,nest_symm hbc,hab⟩ hB
  · have hin := cross_nest_separated_contains (M.proper a) (M.proper b) (M.proper c) hab hbc h
    exact hg.2.1 a b hA (M.container hg hB hin) hab

theorem NB_cross {a b c : ι} (hg : M.LocalGood) (hB : M.B a)
    (hab : M.N a b) (hbc : M.C b c) : M.Q c := by
  have hac : a ≠ c := by
    intro he; subst c
    exact cross_not_nest hbc (M.Nsym hab)
  rcases trichotomy (M.proper a) (M.proper c) (M.apart a c hac) with h | h | h
  · exact Or.inl ⟨a,b,cross_symm h,M.Csym hbc,hab⟩
  · exact (hg.1 a ⟨b,c,hab,h,hbc⟩ hB).elim
  · have hd : Separated (M.arc c) (M.arc a) := h.symm
    have hin := cross_nest_separated_contains (M.proper c) (M.proper b) (M.proper a)
      (M.Csym hbc) (M.Nsym hab) hd
    exact Or.inr ⟨b,M.container hg hB hin,hbc⟩

theorem Q_nonnesting (hg : M.LocalGood) {a b : ι}
    (ha : M.Q a) (hb : M.Q b) : ¬ M.N a b := by
  intro hab
  rcases ha with ha | ⟨s,hs,hsa⟩
  · rcases hb with hb | ⟨s,hs,hsb⟩
    · exact hg.2.2 a b ha hb hab
    · exact M.no_two_link hg hs hsb (M.Nsym hab) ha
  · rcases hb with hb | ⟨t,ht,htb⟩
    · exact M.no_two_link hg hs hsa hab hb
    · rcases M.CNC hsa hab (M.Csym htb) with h | h | h | h
      · exact hg.1 s hs h
      · exact hg.2.1 s a hs h hsa
      · exact hg.2.1 t b ht h htb
      · exact hg.1 t ht h

theorem Q_disjoint_A (hg : M.LocalGood) {a : ι} (hq : M.Q a) : ¬ M.A a := by
  intro ha
  rcases hq with hb | ⟨s,hs,hsa⟩
  · exact hg.1 a ha hb
  · exact hg.2.1 s a hs ha hsa

theorem Q_disjoint_S (hg : M.LocalGood) {a : ι} (hq : M.Q a) : ¬ M.S a := by
  rintro (ha | ⟨q,hqq,hqa⟩)
  · exact M.Q_disjoint_A hg hq ha
  · exact M.Q_nonnesting hg hqq hq hqa

theorem S_cross (hg : M.LocalGood) {a b : ι} (ha : M.S a) (hab : M.C a b) : M.Q b := by
  rcases ha with ha | ⟨q,hq,hqa⟩
  · exact Or.inr ⟨a,ha,hab⟩
  · rcases hq with hq | ⟨s,hs,hsq⟩
    · exact M.NB_cross hg hq hqa hab
    · rcases M.CNC hsq hqa hab with h | h | h | h
      · exact (hg.1 s hs h).elim
      · exact (hg.2.1 s q hs h hsq).elim
      · exact Or.inr ⟨a,h,hab⟩
      · exact Or.inl h


def ValidOn (F : Finset ι) (q : ι → Bool) : Prop :=
 ∀ a ∈ F, ∀ b ∈ F,
  (M.C a b → q a = true ∨ q b = true) ∧
  (M.N a b → q a = false ∨ q b = false)

def TriangleFreeOn (F : Finset ι) : Prop :=
 ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F,
  ¬ ForceS (M.arc a) (M.arc b) (M.arc c) ∧
  ¬ ForceQ (M.arc a) (M.arc b) (M.arc c)

theorem extend_color [DecidableEq ι] {F : Finset ι} {e : ι} {q : ι → Bool}
    (hq : M.ValidOn (F.erase e) q) {color : Bool}
    (hc : ∀ f ∈ F, (M.C e f → color = true) ∧ (M.N e f → color = false)) :
    ∃ q', M.ValidOn F q' := by
  let q' : ι → Bool := fun i => if i = e then color else q i
  refine ⟨q', ?_⟩
  intro a ha b hb
  by_cases hae : a = e
  · subst a
    constructor
    · intro h; exact Or.inl (by simpa [q'] using (hc b hb).1 h)
    · intro h; exact Or.inl (by simpa [q'] using (hc b hb).2 h)
  · by_cases hbe : b = e
    · subst b
      constructor
      · intro h; exact Or.inr (by simpa [q'] using (hc a ha).1 (M.Csym h))
      · intro h; exact Or.inr (by simpa [q'] using (hc a ha).2 (M.Nsym h))
    · simpa [q', hae, hbe] using
        hq a (Finset.mem_erase.mpr ⟨hae,ha⟩) b (Finset.mem_erase.mpr ⟨hbe,hb⟩)

theorem triangle_free_color (F : Finset ι) (hF : M.TriangleFreeOn F) :
    ∃ q, M.ValidOn F q := by
  classical
  revert hF
  refine Finset.strongInductionOn F ?_
  intro F ih hF
  by_cases hn : F.Nonempty
  · obtain ⟨e,he,hmin⟩ := F.exists_min_image (fun i => (M.arc i).hi) hn
    have ltmin : ∀ f ∈ F, f ≠ e → (M.arc e).hi < (M.arc f).hi := by
      intro f hf hfe
      have hle := hmin f hf
      have hneq := (M.apart e f (Ne.symm hfe)).2.2.2
      omega
    have tf : M.TriangleFreeOn (F.erase e) := by
      intro a ha b hb c hc
      exact hF a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
        c (Finset.mem_of_mem_erase hc)
    obtain ⟨q,hq⟩ := ih (F.erase e) (Finset.erase_ssubset he) tf
    by_cases hx : ∃ u ∈ F, M.C e u
    · obtain ⟨u,hu,heu⟩ := hx
      apply M.extend_color hq (color := true)
      intro f hf
      constructor
      · intro _; rfl
      · intro hef
        have hneU : u ≠ e := by intro h; subst u; exact cross_irrefl _ heu
        have hneF : f ≠ e := by intro h; subst f; exact nest_irrefl _ hef
        have huf : u ≠ f := by intro h; subst f; exact cross_not_nest heu hef
        rcases triple_free_extreme (M.proper e) (M.proper u) (M.proper f)
          (ltmin u hu hneU) (ltmin f hf hneF) (M.apart u f huf) heu hef with h | h
        · exact ((hF u hu e he f hf).2 h).elim
        · exact ((hF f hf e he u hu).1 h).elim
    · apply M.extend_color hq (color := false)
      intro f hf
      constructor
      · intro hef; exact (hx ⟨f,hf,hef⟩).elim
      · intro _; rfl
  · have hempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    subst F
    exact ⟨fun _ => false, by simp [ValidOn]⟩

def HasColor : Prop := ∃ q : ι → Bool, ∀ a b,
 (M.C a b → q a = true ∨ q b = true) ∧
 (M.N a b → q a = false ∨ q b = false)

theorem localGood_color [Fintype ι] (hg : M.LocalGood) : M.HasColor := by
  classical
  let U : Finset ι := Finset.univ.filter (fun i => ¬ M.Q i ∧ ¬ M.S i)
  have htf : M.TriangleFreeOn U := by
    intro a ha b _hb c _hc
    have hU := (Finset.mem_filter.mp ha).2
    constructor
    · intro h; exact hU.2 (Or.inl ⟨b,c,h⟩)
    · intro h; exact hU.1 (Or.inl ⟨b,c,h⟩)
  obtain ⟨q,hq⟩ := M.triangle_free_color U htf
  let final : ι → Bool := fun i => if M.Q i then true else if M.S i then false else q i
  refine ⟨final, ?_⟩
  intro a b
  constructor
  · intro hab
    by_cases haQ : M.Q a
    · exact Or.inl (by simp [final,haQ])
    by_cases hbQ : M.Q b
    · exact Or.inr (by simp [final,hbQ])
    have haS : ¬ M.S a := fun h => hbQ (M.S_cross hg h hab)
    have hbS : ¬ M.S b := fun h => haQ (M.S_cross hg h (M.Csym hab))
    have haU : a ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ a,haQ,haS⟩
    have hbU : b ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ b,hbQ,hbS⟩
    simpa [final,haQ,hbQ,haS,hbS] using (hq a haU b hbU).1 hab
  · intro hab
    by_cases haS : M.S a
    · have hnQ : ¬ M.Q a := fun h => M.Q_disjoint_S hg h haS
      exact Or.inl (by simp [final,hnQ,haS])
    by_cases hbS : M.S b
    · have hnQ : ¬ M.Q b := fun h => M.Q_disjoint_S hg h hbS
      exact Or.inr (by simp [final,hnQ,hbS])
    have haQ : ¬ M.Q a := fun h => hbS (Or.inr ⟨a,h,hab⟩)
    have hbQ : ¬ M.Q b := fun h => haS (Or.inr ⟨b,h,M.Nsym hab⟩)
    have haU : a ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ a,haQ,haS⟩
    have hbU : b ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ b,hbQ,hbS⟩
    simpa [final,haQ,hbQ,haS,hbS] using (hq a haU b hbU).2 hab

theorem A_color {q : ι → Bool}
    (hq : ∀ a b, (M.C a b → q a = true ∨ q b = true) ∧
      (M.N a b → q a = false ∨ q b = false)) {a : ι} (ha : M.A a) : q a = false := by
  obtain ⟨u,v,h⟩ := ha
  have h1 := (hq a u).2 h.1
  have h2 := (hq a v).2 h.2.1
  have h3 := (hq u v).1 h.2.2
  cases hi : q a <;> cases hj : q u <;> cases hk : q v <;> simp_all

theorem B_color {q : ι → Bool}
    (hq : ∀ a b, (M.C a b → q a = true ∨ q b = true) ∧
      (M.N a b → q a = false ∨ q b = false)) {a : ι} (ha : M.B a) : q a = true := by
  obtain ⟨u,v,h⟩ := ha
  have h1 := (hq a u).1 h.1
  have h2 := (hq a v).1 h.2.1
  have h3 := (hq u v).2 h.2.2
  cases hi : q a <;> cases hj : q u <;> cases hk : q v <;> simp_all

theorem color_localGood (h : M.HasColor) : M.LocalGood := by
  obtain ⟨q,hq⟩ := h
  refine ⟨?_,?_,?_⟩
  · intro a ha hb
    have h0 := M.A_color hq ha
    have h1 := M.B_color hq hb
    simp [h0] at h1
  · intro a b ha hb hab
    have h0 := M.A_color hq ha
    have h1 := M.A_color hq hb
    have hv := (hq a b).1 hab
    simp [h0,h1] at hv
  · intro a b ha hb hab
    have h0 := M.B_color hq ha
    have h1 := M.B_color hq hb
    have hv := (hq a b).2 hab
    simp [h0,h1] at hv

/-- Unbounded, literal finite-matching coloring criterion. -/
theorem coloring_criterion [Fintype ι] : M.HasColor ↔ M.LocalGood :=
 ⟨M.color_localGood, M.localGood_color⟩

#print axioms S_cross
#print axioms Q_disjoint_S
#print axioms triangle_free_color
#print axioms localGood_color
#print axioms coloring_criterion
end OrderedMatching
end Pool039
```

### `SmallCore.lean`

```lean
import Criterion
set_option maxHeartbeats 0
namespace Pool039.OrderedMatching
variable {ι : Type} (M : Pool039.OrderedMatching ι)

def restrict (H : Finset ι) : Pool039.OrderedMatching {i // i ∈ H} where
 arc i := M.arc i.val
 proper i := M.proper i.val
 apart i j h := M.apart i.val j.val (fun he => h (Subtype.ext he))

theorem both_bad {a : ι} (ha : M.A a) (hb : M.B a) : ¬ M.HasColor :=
 fun h => (M.color_localGood h).1 a ha hb

theorem SS_bad {a b : ι} (ha : M.A a) (hb : M.A b) (hab : M.C a b) : ¬ M.HasColor :=
 fun h => (M.color_localGood h).2.1 a b ha hb hab

theorem QQ_bad {a b : ι} (ha : M.B a) (hb : M.B b) (hab : M.N a b) : ¬ M.HasColor :=
 fun h => (M.color_localGood h).2.2 a b ha hb hab

theorem same_core {a u v x y : ι}
    (hs : ForceS (M.arc a) (M.arc u) (M.arc v))
    (hq : ForceQ (M.arc a) (M.arc x) (M.arc y)) :
    ∃ H : Finset ι, H.card ≤ 6 ∧ ¬ (M.restrict H).HasColor := by
  classical
  let H := ([a,u,v,x,y] : List ι).toFinset
  have hcard : H.card ≤ 6 := by
    have h := List.toFinset_card_le (l := ([a,u,v,x,y] : List ι))
    simpa [H] using Nat.le_trans h (by decide : 5 ≤ 6)
  refine ⟨H,hcard,?_⟩
  let aa : {i // i ∈ H} := ⟨a,by simp [H]⟩
  have hA : (M.restrict H).A aa := ⟨⟨u,by simp [H]⟩,⟨v,by simp [H]⟩,hs⟩
  have hB : (M.restrict H).B aa := ⟨⟨x,by simp [H]⟩,⟨y,by simp [H]⟩,hq⟩
  exact (M.restrict H).both_bad hA hB

theorem SS_core {a u v b x y : ι}
    (ha : ForceS (M.arc a) (M.arc u) (M.arc v))
    (hb : ForceS (M.arc b) (M.arc x) (M.arc y)) (hab : M.C a b) :
    ∃ H : Finset ι, H.card ≤ 6 ∧ ¬ (M.restrict H).HasColor := by
  classical
  let H := ([a,u,v,b,x,y] : List ι).toFinset
  have hcard : H.card ≤ 6 := by
    simpa [H] using List.toFinset_card_le (l := ([a,u,v,b,x,y] : List ι))
  refine ⟨H,hcard,?_⟩
  let aa : {i // i ∈ H} := ⟨a,by simp [H]⟩
  let bb : {i // i ∈ H} := ⟨b,by simp [H]⟩
  have hA : (M.restrict H).A aa := ⟨⟨u,by simp [H]⟩,⟨v,by simp [H]⟩,ha⟩
  have hB : (M.restrict H).A bb := ⟨⟨x,by simp [H]⟩,⟨y,by simp [H]⟩,hb⟩
  exact (M.restrict H).SS_bad hA hB hab

theorem QQ_core {a u v b x y : ι}
    (ha : ForceQ (M.arc a) (M.arc u) (M.arc v))
    (hb : ForceQ (M.arc b) (M.arc x) (M.arc y)) (hab : M.N a b) :
    ∃ H : Finset ι, H.card ≤ 6 ∧ ¬ (M.restrict H).HasColor := by
  classical
  let H := ([a,u,v,b,x,y] : List ι).toFinset
  have hcard : H.card ≤ 6 := by
    simpa [H] using List.toFinset_card_le (l := ([a,u,v,b,x,y] : List ι))
  refine ⟨H,hcard,?_⟩
  let aa : {i // i ∈ H} := ⟨a,by simp [H]⟩
  let bb : {i // i ∈ H} := ⟨b,by simp [H]⟩
  have hA : (M.restrict H).B aa := ⟨⟨u,by simp [H]⟩,⟨v,by simp [H]⟩,ha⟩
  have hB : (M.restrict H).B bb := ⟨⟨x,by simp [H]⟩,⟨y,by simp [H]⟩,hb⟩
  exact (M.restrict H).QQ_bad hA hB hab

/-- Honest unbounded six-edge obstruction theorem; the size bound is a conclusion. -/
theorem six_edge_core [Fintype ι] (h : ¬ M.HasColor) :
    ∃ H : Finset ι, H.card ≤ 6 ∧ ¬ (M.restrict H).HasColor := by
  classical
  have hn : ¬ M.LocalGood := fun hg => h (M.localGood_color hg)
  simp only [LocalGood, not_and_or] at hn
  rcases hn with hn | hn | hn
  · push Not at hn
    obtain ⟨a,⟨u,v,hs⟩,x,y,hq⟩ := hn
    exact M.same_core hs hq
  · push Not at hn
    obtain ⟨a,b,⟨u,v,ha⟩,⟨x,y,hb⟩,hab⟩ := hn
    exact M.SS_core ha hb hab
  · push Not at hn
    obtain ⟨a,b,⟨u,v,ha⟩,⟨x,y,hb⟩,hab⟩ := hn
    exact M.QQ_core ha hb hab
#print axioms six_edge_core
end Pool039.OrderedMatching
```

### `FiniteDefs.lean`

```lean
import Mathlib.Data.List.Sort
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
abbrev Arc := ℕ × ℕ

def cross (a b : Arc) : Bool :=
 (a.1 < b.1 && b.1 < a.2 && a.2 < b.2) ||
 (b.1 < a.1 && a.1 < b.2 && b.2 < a.2)
def nest (a b : Arc) : Bool :=
 (a.1 < b.1 && b.2 < a.2) || (b.1 < a.1 && a.2 < b.2)

def firstGood (a : Arc) (queue : Bool) : List Arc → ℕ → Bool
 | [], _ => true
 | b :: E, mask =>
   (!(if queue then mask % 2 == 1 && nest a b
       else mask % 2 == 0 && cross a b)) &&
     firstGood a queue E (mask / 2)

def goodMask : List Arc → ℕ → Bool
 | [], _ => true
 | a :: E, mask => firstGood a (mask % 2 == 1) E (mask / 2) && goodMask E (mask / 2)

def hasSQ (E : List Arc) : Bool :=
 (List.range (2 ^ E.length)).any (goodMask E)

def matchings : ℕ → List ℕ → List (List Arc)
 | 0, xs => if xs.isEmpty then [[]] else []
 | _fuel+1, [] => []
 | fuel+1, a::xs => xs.flatMap fun b =>
     (matchings fuel (xs.erase b)).map (fun E => (a,b)::E)

def eraseEach (E : List Arc) : List (List Arc) :=
 (List.range E.length).map E.eraseIdx

def sourceSQ : List (List Arc) := [
 [(0,5), (1,4), (2,7), (3,6)],
 [(0,7), (1,4), (2,9), (3,6), (5,8)],
 [(0,6), (1,7), (2,4), (3,5)],
 [(0,6), (1,3), (2,4), (5,11), (7,9), (8,10)],
 [(0,6), (1,3), (2,9), (4,7), (5,8)],
 [(0,7), (1,4), (2,5), (3,9), (6,8)],
 [(0,7), (1,4), (2,9), (3,5), (6,8)],
 [(0,7), (1,3), (2,9), (4,6), (5,8)],
 [(0,5), (1,3), (2,9), (4,7), (6,8)],
 [(0,7), (1,3), (2,5), (4,9), (6,8)],
 [(0,7), (1,3), (2,4), (5,9), (6,8)],
 [(0,4), (1,3), (2,9), (5,7), (6,8)]
]

/-- Every non-basis matching up to six edges is colorable or has an uncolorable deletion.
This is only the finite computation; source-scope bridges are not asserted here. -/
def checkMatching (E : List Arc) : Bool :=
 hasSQ E || sourceSQ.contains E || (eraseEach E).any (fun F => !hasSQ F)

def finiteCheck (n : ℕ) : Bool :=
 (matchings n (List.range (2*n))).all checkMatching


def branchCheck6 (b : ℕ) : Bool :=
  ((matchings 5 ((List.range 12).erase 0 |>.erase b)).map
    (fun E => (0,b)::E)).all checkMatching
def prefixCheck6 (P : List Arc) (xs : List ℕ) : Bool :=
 ((matchings 4 xs).map (fun E => P ++ E)).all checkMatching

def select : List Arc → ℕ → List Arc
 | [], _ => []
 | a::E, m => if m % 2 == 1 then a :: select E (m/2) else select E (m/2)
def normalize (E : List Arc) : List Arc :=
 let endpoints := E.flatMap (fun p => [p.1,p.2])
 E.map (fun p => ((endpoints.filter (· < p.1)).length,
                 (endpoints.filter (· < p.2)).length))
def checkRow (E : List Arc) (code : ℕ) : Bool :=
 if code % 2 == 0 then goodMask E (code/2)
 else sourceSQ.contains (normalize (select E (code/2)))
def checkRows : List (List Arc) → List ℕ → Bool
 | [], [] => true
 | E::es, c::cs => checkRow E c && checkRows es cs
 | _, _ => false

end Pool039Finite
```

### `RankNormalization.lean`

```lean
import Criterion
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Prod

set_option maxHeartbeats 0
namespace Pool039

def endpt (a : Arc) (s : Bool) : ℕ := if s then a.hi else a.lo

namespace OrderedMatching
variable {ι : Type} (M : OrderedMatching ι)

/-- The original vertex positions, including both endpoints of every edge. -/
def position (p : ι × Bool) : ℕ := endpt (M.arc p.1) p.2

theorem position_injective : Function.Injective M.position := by
  intro ⟨i,s⟩ ⟨j,t⟩ h
  have hij : i = j := by
    by_contra hn
    have ha := M.apart i j hn
    cases s <;> cases t <;> simp [position, endpt] at h <;> simp_all [Apart]
  subst j
  have hp := M.proper i
  have hst : s = t := by
    cases s <;> cases t <;> simp_all [position, endpt]
  subst t
  rfl

variable [Fintype ι]
noncomputable def positions : Finset ℕ := by
  classical
  exact Finset.univ.image M.position

theorem card_positions : M.positions.card = 2 * Fintype.card ι := by
  classical
  rw [positions, Finset.card_image_of_injective _ M.position_injective]
  simp [Fintype.card_prod, Nat.mul_comm]

noncomputable def rank (p : ι × Bool) : Fin (2 * Fintype.card ι) :=
  (M.positions.orderIsoOfFin M.card_positions).symm
    ⟨M.position p, by classical exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩

theorem rank_lt_iff (p q : ι × Bool) : M.rank p < M.rank q ↔ M.position p < M.position q := by
  exact (M.positions.orderIsoOfFin M.card_positions).symm.lt_iff_lt

theorem rank_injective : Function.Injective M.rank := by
  intro p q h
  apply M.position_injective
  have he := congrArg (M.positions.orderIsoOfFin M.card_positions) h
  simpa only [rank, OrderIso.apply_symm_apply] using congrArg Subtype.val he

theorem rank_surjective : Function.Surjective M.rank := by
  classical
  intro r
  let v := M.positions.orderIsoOfFin M.card_positions r
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp v.property
  refine ⟨p, ?_⟩
  apply (M.positions.orderIsoOfFin M.card_positions).injective
  apply Subtype.ext
  simpa [rank, v] using hp

noncomputable def ranked : OrderedMatching ι where
  arc i := ⟨M.rank (i,false), M.rank (i,true)⟩
  proper i := (M.rank_lt_iff _ _).mpr (M.proper i)
  apart i j hij := by
    have h : ∀ s t, (M.rank (i,s)).val ≠ (M.rank (j,t)).val := by
      intro s t he
      exact hij (congrArg Prod.fst (M.rank_injective (Fin.ext he)))
    exact ⟨h false false, h false true, h true false, h true true⟩

theorem ranked_endpt (i : ι) (s : Bool) : endpt (M.ranked.arc i) s = M.rank (i,s) := by
  cases s <;> rfl

theorem ranked_comparison (i j : ι) (s t : Bool) :
    endpt (M.ranked.arc i) s < endpt (M.ranked.arc j) t ↔
      endpt (M.arc i) s < endpt (M.arc j) t := by
  simp only [ranked_endpt]
  simpa only [Fin.lt_def, position] using M.rank_lt_iff (i,s) (j,t)

/-- Comparison preservation includes all four kinds of endpoint comparisons. -/
theorem ranked_cross (i j : ι) :
    Cross (M.ranked.arc i) (M.ranked.arc j) ↔ Cross (M.arc i) (M.arc j) := by
  change ((endpt (M.ranked.arc i) false < endpt (M.ranked.arc j) false ∧
    endpt (M.ranked.arc j) false < endpt (M.ranked.arc i) true ∧
    endpt (M.ranked.arc i) true < endpt (M.ranked.arc j) true) ∨
    (endpt (M.ranked.arc j) false < endpt (M.ranked.arc i) false ∧
    endpt (M.ranked.arc i) false < endpt (M.ranked.arc j) true ∧
    endpt (M.ranked.arc j) true < endpt (M.ranked.arc i) true)) ↔ _
  simp only [ranked_comparison]
  rfl

theorem ranked_nest (i j : ι) :
    Nest (M.ranked.arc i) (M.ranked.arc j) ↔ Nest (M.arc i) (M.arc j) := by
  change ((endpt (M.ranked.arc i) false < endpt (M.ranked.arc j) false ∧
    endpt (M.ranked.arc j) true < endpt (M.ranked.arc i) true) ∨
    (endpt (M.ranked.arc j) false < endpt (M.ranked.arc i) false ∧
    endpt (M.ranked.arc i) true < endpt (M.ranked.arc j) true)) ↔ _
  simp only [ranked_comparison]
  rfl

theorem ranked_hasColor : M.ranked.HasColor ↔ M.HasColor := by
  simp only [HasColor, C, N, ranked_cross, ranked_nest]

end OrderedMatching
end Pool039
```

### `EnumeratorCompleteness.lean`

```lean
import FiniteDefs
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Perm.Basic
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
namespace Pool039Finite

def endpoints (E : List Arc) : List ℕ := E.flatMap (fun p => [p.1,p.2])

theorem mem_endpoints {x : ℕ} {E : List Arc} :
    x ∈ endpoints E ↔ ∃ p ∈ E, x = p.1 ∨ x = p.2 := by
  simp [endpoints]

/-- Completeness for every size, not just the six-edge certificate range.
A list of proper arcs sorted by left endpoint is enumerated on its sorted endpoint set. -/
theorem mem_matchings_of_sorted (E : List Arc) (xs : List ℕ)
    (hproper : ∀ p ∈ E, p.1 < p.2)
    (hsorted : E.Pairwise (fun p q => p.1 < q.1))
    (hxsorted : xs.Pairwise (· < ·)) (hp : xs.Perm (endpoints E)) :
    E ∈ matchings E.length xs := by
  induction E generalizing xs with
  | nil =>
    have he : xs = [] := hp.eq_nil
    subst xs
    simp [matchings]
  | cons p E ih =>
    have hp0 := hproper p (by simp)
    have hpr : ∀ q ∈ E, q.1 < q.2 := fun q hq => hproper q (by simp [hq])
    obtain ⟨hpmin, hsort⟩ := List.pairwise_cons.mp hsorted
    have hmin : ∀ x ∈ endpoints (p::E), p.1 ≤ x := by
      intro x hx
      obtain ⟨q,hq,hx | hx⟩ := mem_endpoints.mp hx
      · subst x
        rcases List.mem_cons.mp hq with h | h
        · subst q; exact Nat.le_refl _
        · exact Nat.le_of_lt (hpmin q h)
      · subst x
        rcases List.mem_cons.mp hq with h | h
        · subst q; exact Nat.le_of_lt hp0
        · exact Nat.le_trans (Nat.le_of_lt (hpmin q h)) (Nat.le_of_lt (hpr q h))
    cases xs with
    | nil =>
      have hmem : p.1 ∈ endpoints (p::E) := mem_endpoints.mpr ⟨p,by simp,Or.inl rfl⟩
      have := hp.mem_iff.mpr hmem
      simp at this
    | cons a xs =>
      have hleft : a = p.1 := by
        have ha : p.1 ≤ a := hmin a (hp.mem_iff.mp (by simp))
        have hp1 : p.1 ∈ a::xs := hp.mem_iff.mpr (mem_endpoints.mpr ⟨p,by simp,Or.inl rfl⟩)
        have hb : a ≤ p.1 := by
          rcases List.mem_cons.mp hp1 with he | he
          · omega
          · exact Nat.le_of_lt ((List.pairwise_cons.mp hxsorted).1 _ he)
        omega
      subst a
      have hbmem : p.2 ∈ xs := by
        have h := hp.mem_iff.mpr (mem_endpoints.mpr ⟨p,by simp,Or.inr rfl⟩)
        rcases List.mem_cons.mp h with h | h
        · omega
        · exact h
      have hp' : xs.Perm (p.2 :: endpoints E) := by
        apply List.Perm.cons_inv (a := p.1)
        simpa only [endpoints, List.flatMap_cons, List.cons_append, List.nil_append] using hp
      have hp'' : (xs.erase p.2).Perm (endpoints E) := by
        simpa using hp'.erase p.2
      have hr := ih (xs.erase p.2) hpr hsort
        ((List.pairwise_cons.mp hxsorted).2.sublist (List.erase_sublist)) hp''
      simp only [List.length_cons, matchings, List.mem_flatMap, List.mem_map]
      exact ⟨p.2, hbmem, E, hr, by cases p; rfl⟩

#print axioms mem_matchings_of_sorted
end Pool039Finite
```

### `CanonicalRow.lean`

```lean
import RankNormalization
import EnumeratorCompleteness
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Card

set_option maxHeartbeats 0
namespace Pool039.OrderedMatching
variable {ι : Type} [Fintype ι] (M : Pool039.OrderedMatching ι)

omit [Fintype ι] in
theorem lo_injective : Function.Injective (fun i => (M.arc i).lo) := by
  intro i j h
  by_contra hn
  exact (M.apart i j hn).1 h

/-- Edges listed in increasing left-endpoint order. -/
noncomputable def edgeList : List ι := by
  classical
  let := LinearOrder.lift' (fun i => (M.arc i).lo) M.lo_injective
  exact Finset.univ.sort

theorem edgeList_length : M.edgeList.length = Fintype.card ι := by
  classical
  unfold edgeList
  simp

theorem edgeList_nodup : M.edgeList.Nodup := by
  classical
  unfold edgeList
  exact Finset.sort_nodup _ _

theorem mem_edgeList (i : ι) : i ∈ M.edgeList := by
  classical
  unfold edgeList
  simp

theorem edgeList_sorted : M.edgeList.Pairwise (fun i j => (M.arc i).lo < (M.arc j).lo) := by
  classical
  let := LinearOrder.lift' (fun i => (M.arc i).lo) M.lo_injective
  exact Finset.univ.sortedLT_sort.pairwise

noncomputable def canonicalRow : List Pool039Finite.Arc :=
  M.edgeList.map (fun i => ((M.rank (i,false)).val, (M.rank (i,true)).val))

theorem canonicalRow_length : M.canonicalRow.length = Fintype.card ι := by
  simp [canonicalRow, edgeList_length]

theorem canonicalRow_proper : ∀ p ∈ M.canonicalRow, p.1 < p.2 := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact (M.rank_lt_iff _ _).mpr (M.proper i)

theorem canonicalRow_sorted : M.canonicalRow.Pairwise (fun p q => p.1 < q.1) := by
  apply List.pairwise_map.mpr
  apply M.edgeList_sorted.imp
  intro i j hij
  exact (M.rank_lt_iff _ _).mpr hij

theorem canonicalRow_endpoints_mem (x : ℕ) :
    x ∈ Pool039Finite.endpoints M.canonicalRow ↔ x < 2 * Fintype.card ι := by
  constructor
  · intro hx
    obtain ⟨p,hp,hx | hx⟩ := Pool039Finite.mem_endpoints.mp hx <;>
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp <;> subst x
    · exact (M.rank (i,false)).isLt
    · exact (M.rank (i,true)).isLt
  · intro hx
    obtain ⟨⟨i,s⟩,h⟩ := M.rank_surjective ⟨x,hx⟩
    apply Pool039Finite.mem_endpoints.mpr
    refine ⟨_, List.mem_map.mpr ⟨i,M.mem_edgeList i,rfl⟩, ?_⟩
    cases s
    · exact Or.inl (congrArg Fin.val h).symm
    · exact Or.inr (congrArg Fin.val h).symm

theorem canonicalRow_endpoints_length :
    (Pool039Finite.endpoints M.canonicalRow).length = 2 * Fintype.card ι := by
  have h : ∀ E : List Pool039Finite.Arc,
      (Pool039Finite.endpoints E).length = 2 * E.length := by
    intro E
    induction E with
    | nil => rfl
    | cons p E ih => simp [Pool039Finite.endpoints] at ih ⊢; omega
  rw [h, M.canonicalRow_length]

theorem canonicalRow_endpoints_perm :
    (List.range (2 * Fintype.card ι)).Perm (Pool039Finite.endpoints M.canonicalRow) := by
  refine ((List.nodup_range).subperm ?_).perm_of_length_le ?_
  · intro x hx
    exact (M.canonicalRow_endpoints_mem x).mpr (List.mem_range.mp hx)
  · simp [canonicalRow_endpoints_length]

theorem canonicalRow_mem :
    M.canonicalRow ∈ Pool039Finite.matchings (Fintype.card ι)
      (List.range (2 * Fintype.card ι)) := by
  rw [← M.canonicalRow_length] at ⊢
  apply Pool039Finite.mem_matchings_of_sorted
  · exact M.canonicalRow_proper
  · exact M.canonicalRow_sorted
  · exact (List.sortedLT_range _).pairwise
  · simpa only [M.canonicalRow_length] using M.canonicalRow_endpoints_perm

/-- Explicit edge bijection; no vertices or endpoint comparisons are forgotten. -/
noncomputable def canonicalEquiv : Fin M.canonicalRow.length ≃ ι := by
  classical
  exact (finCongr (by simp only [canonicalRow, List.length_map])).trans
    (M.edgeList_nodup.getEquivOfForallMemList M.edgeList M.mem_edgeList)

theorem canonicalEquiv_arc (i : Fin M.canonicalRow.length) :
    (⟨M.canonicalRow[i].1, M.canonicalRow[i].2⟩ : Pool039.Arc) =
      M.ranked.arc (M.canonicalEquiv i) := by
  unfold canonicalRow at i
  simp only [canonicalRow, Fin.getElem_fin, List.getElem_map]
  rfl

theorem canonicalEquiv_comparison (i j : Fin M.canonicalRow.length) (s t : Bool) :
    Pool039.endpt ⟨M.canonicalRow[i].1,M.canonicalRow[i].2⟩ s <
        Pool039.endpt ⟨M.canonicalRow[j].1,M.canonicalRow[j].2⟩ t ↔
      Pool039.endpt (M.arc (M.canonicalEquiv i)) s <
        Pool039.endpt (M.arc (M.canonicalEquiv j)) t := by
  rw [M.canonicalEquiv_arc, M.canonicalEquiv_arc]
  exact M.ranked_comparison _ _ _ _

#print axioms canonicalRow_mem
#print axioms canonicalEquiv_comparison
end Pool039.OrderedMatching
```

### `EndpointTransport.lean`

```lean
import CanonicalRow
import SmallCore

set_option maxHeartbeats 0
namespace Pool039

/-- The source's literal order-preserving submatching relation. -/
def Contains {ι : Type} (M : OrderedMatching ι) (P : List Arc) : Prop :=
  ∃ f : Fin P.length → ι, Function.Injective f ∧ ∀ i j : Fin P.length, ∀ s t : Bool,
    (endpt P[i] s < endpt P[j] t ↔ endpt (M.arc (f i)) s < endpt (M.arc (f j)) t)

def OneStackOneQueue {ι : Type} (M : OrderedMatching ι) : Prop :=
  ∃ isQueue : ι → Bool, ∀ a b, a ≠ b →
    (Cross (M.arc a) (M.arc b) → isQueue a ∨ isQueue b) ∧
    (Nest (M.arc a) (M.arc b) → ¬isQueue a ∨ ¬isQueue b)

def OneMixedPage {ι : Type} (M : OrderedMatching ι) : Prop :=
  (∀ a b, ¬Cross (M.arc a) (M.arc b)) ∨ (∀ a b, ¬Nest (M.arc a) (M.arc b))

def fig19a : List (List Arc) := sourceSQ
def fig19b : List (List Arc) := sourceOne

theorem cross_endpt (a b : Arc) : Cross a b ↔
    (endpt a false < endpt b false ∧ endpt b false < endpt a true ∧
      endpt a true < endpt b true) ∨
    (endpt b false < endpt a false ∧ endpt a false < endpt b true ∧
      endpt b true < endpt a true) := Iff.rfl

theorem nest_endpt (a b : Arc) : Nest a b ↔
    (endpt a false < endpt b false ∧ endpt b true < endpt a true) ∨
    (endpt b false < endpt a false ∧ endpt a true < endpt b true) := Iff.rfl

theorem comparisons_cross {α : Type} (A B : α → Arc)
    (h : ∀ i j s t, endpt (A i) s < endpt (A j) t ↔ endpt (B i) s < endpt (B j) t)
    (i j : α) : Cross (A i) (A j) ↔ Cross (B i) (B j) := by
  simp only [cross_endpt, h]

theorem comparisons_nest {α : Type} (A B : α → Arc)
    (h : ∀ i j s t, endpt (A i) s < endpt (A j) t ↔ endpt (B i) s < endpt (B j) t)
    (i j : α) : Nest (A i) (A j) ↔ Nest (B i) (B j) := by
  simp only [nest_endpt, h]

def rowArc (E : List Pool039Finite.Arc) (i : Fin E.length) : Arc := ⟨E[i].1,E[i].2⟩

def RowColor (E : List Pool039Finite.Arc) : Prop :=
  ∃ q : Fin E.length → Bool, ∀ a b,
    (Cross (rowArc E a) (rowArc E b) → q a = true ∨ q b = true) ∧
    (Nest (rowArc E a) (rowArc E b) → q a = false ∨ q b = false)

def RowContains (E : List Pool039Finite.Arc) (P : List Arc) : Prop :=
  ∃ f : Fin P.length → Fin E.length, Function.Injective f ∧ ∀ i j s t,
    (endpt P[i] s < endpt P[j] t ↔
      endpt (rowArc E (f i)) s < endpt (rowArc E (f j)) t)

/-- An enumerator row faithfully presents every edge and every endpoint comparison. -/
def Presents {ι : Type} (M : OrderedMatching ι) (E : List Pool039Finite.Arc) : Prop :=
  ∃ e : Fin E.length ≃ ι, ∀ i j s t,
    endpt (rowArc E i) s < endpt (rowArc E j) t ↔
      endpt (M.arc (e i)) s < endpt (M.arc (e j)) t

namespace OrderedMatching
variable {ι : Type} (M : OrderedMatching ι)

theorem oneStackOneQueue_iff_hasColor : OneStackOneQueue M ↔ M.HasColor := by
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨q, fun a b => ?_⟩
    by_cases he : a = b
    · subst b
      exact ⟨fun h => (cross_irrefl _ h).elim, fun h => (nest_irrefl _ h).elim⟩
    · simpa only [Bool.not_eq_true, C, N] using hq a b he
  · rintro ⟨q,hq⟩
    exact ⟨q, fun a b _ => by simpa only [Bool.not_eq_true, C, N] using hq a b⟩

theorem canonical_presents [Fintype ι] : Presents M M.canonicalRow :=
  ⟨M.canonicalEquiv, M.canonicalEquiv_comparison⟩

theorem presents_color {E} (h : Presents M E) : RowColor E ↔ M.HasColor := by
  obtain ⟨e,he⟩ := h
  have hC := comparisons_cross (rowArc E) (fun i => M.arc (e i)) he
  have hN := comparisons_nest (rowArc E) (fun i => M.arc (e i)) he
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨fun i => q (e.symm i), fun a b => ?_⟩
    simpa only [e.apply_symm_apply, C, N] using
      And.intro (fun h => (hq (e.symm a) (e.symm b)).1 ((hC _ _).mpr h))
        (fun h => (hq (e.symm a) (e.symm b)).2 ((hN _ _).mpr h))
  · rintro ⟨q,hq⟩
    exact ⟨fun i => q (e i), fun a b =>
      ⟨fun h => (hq (e a) (e b)).1 ((hC a b).mp h),
       fun h => (hq (e a) (e b)).2 ((hN a b).mp h)⟩⟩

theorem presents_contains {E} (h : Presents M E) (P : List Arc) :
    RowContains E P ↔ Contains M P := by
  obtain ⟨e,he⟩ := h
  constructor
  · rintro ⟨f,hf,hcomp⟩
    exact ⟨fun i => e (f i), e.injective.comp hf,
      fun i j s t => (hcomp i j s t).trans (he (f i) (f j) s t)⟩
  · rintro ⟨f,hf,hcomp⟩
    refine ⟨fun i => e.symm (f i), e.symm.injective.comp hf, fun i j s t => ?_⟩
    exact (hcomp i j s t).trans (by simpa using (he (e.symm (f i)) (e.symm (f j)) s t).symm)

/-- Bridge (c), with no bound on the original matching or the enumerator size. -/
theorem enumerated_presentation [Fintype ι] :
    ∃ E ∈ Pool039Finite.matchings (Fintype.card ι) (List.range (2 * Fintype.card ι)),
      E.length = Fintype.card ι ∧ Presents M E ∧
      (RowColor E ↔ M.HasColor) ∧ (∀ P, RowContains E P ↔ Contains M P) :=
  ⟨M.canonicalRow, M.canonicalRow_mem, M.canonicalRow_length, M.canonical_presents,
    M.presents_color M.canonical_presents, M.presents_contains M.canonical_presents⟩

/-- The derived six-edge conclusion is not an endpoint hypothesis. -/
theorem enumerated_bad_core [Fintype ι] (h : ¬ M.HasColor) :
    ∃ m ≤ 6, ∃ E ∈ Pool039Finite.matchings m (List.range (2*m)),
      ¬ RowColor E ∧ ∀ P, RowContains E P → Contains M P := by
  classical
  obtain ⟨H,hcard,hbad⟩ := M.six_edge_core h
  obtain ⟨E,hE,_,hp,hcolor,hcont⟩ := (M.restrict H).enumerated_presentation
  refine ⟨H.card,hcard,E,?_, fun hc => hbad (hcolor.mp hc),?_⟩
  · simpa using hE
  · intro P hP
    obtain ⟨f,hf,hcmp⟩ := (hcont P).mp hP
    exact ⟨fun i => (f i).val, Subtype.val_injective.comp hf, hcmp⟩

#print axioms enumerated_presentation
#print axioms enumerated_bad_core
end OrderedMatching
end Pool039
```

### `CertificateChunk0.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_0 : List ℕ := [0,32,0,16,32,16,0,48,16,16,64,16,0,32,0,8,40,8,16,40,16,8,48,16,16,72,16,8,40,8,0,32,0,24,40,24,8,48,24,24,72,24,8,40,8,8,32,8,32,32,32,8,56,24,16,72,24,8,40,8,0,40,8,16,40,40,0,96,121,24,72,24,8,72,8,8,64,8,80,80,32,8,80,48,64,64,32,8,121,8,0,32,0,16,32,16,0,48,16,16,64,16,0,32,0]
theorem certificate_chunk_0 :
 checkRows ((matchings 4 [4,5,6,7,8,9,10,11]).map (fun E => [(0,1),(2,3)] ++ E)) codes_0 = true := by decide +kernel
#print axioms certificate_chunk_0
end Pool039Finite
```

### `CertificateChunk1.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_1 : List ℕ := [4,36,4,20,36,20,4,52,20,20,68,20,4,36,4,8,40,8,20,40,20,8,52,20,20,72,20,8,40,8,4,36,4,24,40,24,8,52,24,24,72,24,8,40,8,8,36,8,36,36,36,8,56,24,20,72,24,8,40,8,4,40,8,20,40,40,4,100,121,24,72,24,8,72,8,8,68,8,84,84,36,8,84,52,68,68,36,8,121,8,4,36,4,20,36,20,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_1 :
 checkRows ((matchings 4 [3,5,6,7,8,9,10,11]).map (fun E => [(0,1),(2,4)] ++ E)) codes_1 = true := by decide +kernel
#print axioms certificate_chunk_1
end Pool039Finite
```

### `CertificateChunk10.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_10 : List ℕ := [4,36,4,20,36,20,4,52,20,20,68,20,4,36,4,10,42,10,20,42,20,10,52,20,20,74,20,10,42,10,4,36,4,26,42,26,10,52,26,26,74,26,10,42,10,10,36,10,36,36,36,10,58,26,20,74,26,10,42,10,4,42,10,20,42,42,4,100,121,26,74,26,10,74,10,10,68,10,84,84,36,10,84,52,68,68,36,10,121,10,4,36,4,20,36,20,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_10 :
 checkRows ((matchings 4 [3,5,6,7,8,9,10,11]).map (fun E => [(0,2),(1,4)] ++ E)) codes_10 = true := by decide +kernel
#print axioms certificate_chunk_10
end Pool039Finite
```

### `CertificateChunk11.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_11 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,12,44,12,20,44,20,12,52,20,20,76,20,12,44,12,4,36,4,26,44,26,12,52,26,26,76,26,12,44,12,12,36,12,36,36,36,12,58,26,20,76,26,12,44,12,4,44,12,20,44,44,4,100,121,26,76,26,12,76,12,12,68,12,84,84,36,12,84,52,68,68,36,12,121,12,4,36,4,20,36,20,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_11 :
 checkRows ((matchings 4 [3,4,6,7,8,9,10,11]).map (fun E => [(0,2),(1,5)] ++ E)) codes_11 = true := by decide +kernel
#print axioms certificate_chunk_11
end Pool039Finite
```

### `CertificateChunk12.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_12 : List ℕ := [4,36,4,18,36,18,4,50,18,18,68,18,4,36,4,18,50,18,18,50,18,18,50,18,18,82,18,18,125,18,4,36,4,28,44,28,12,52,28,28,76,28,12,44,12,10,36,10,36,36,36,12,58,28,20,76,28,12,44,12,4,42,10,20,44,44,4,100,121,28,76,28,12,76,12,10,68,10,84,84,36,12,84,52,68,68,36,12,121,12,4,36,4,20,36,20,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_12 :
 checkRows ((matchings 4 [3,4,5,7,8,9,10,11]).map (fun E => [(0,2),(1,6)] ++ E)) codes_12 = true := by decide +kernel
#print axioms certificate_chunk_12
end Pool039Finite
```

### `CertificateChunk13.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_13 : List ℕ := [2,34,2,20,36,20,4,50,20,20,68,20,4,36,4,10,42,10,20,50,20,20,50,20,20,84,20,20,125,20,2,34,2,50,50,50,61,50,50,61,61,50,61,61,61,12,36,12,36,36,36,12,60,28,20,76,28,12,44,12,4,42,12,36,42,42,4,100,121,26,76,28,12,76,12,12,68,12,100,100,36,12,84,52,68,68,36,12,121,12,4,36,4,36,36,36,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_13 :
 checkRows ((matchings 4 [3,4,5,6,8,9,10,11]).map (fun E => [(0,2),(1,7)] ++ E)) codes_13 = true := by decide +kernel
#print axioms certificate_chunk_13
end Pool039Finite
```

### `CertificateChunk14.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_14 : List ℕ := [4,34,4,34,34,34,4,52,20,18,68,20,4,36,4,42,42,42,42,42,42,18,52,20,18,84,20,18,125,20,4,34,4,42,42,42,26,52,52,26,61,52,26,61,61,34,34,34,34,34,34,18,114,109,18,61,93,18,61,61,4,44,12,61,44,44,4,100,117,28,76,28,12,76,12,10,68,12,61,100,36,10,100,117,68,68,36,12,121,12,4,36,4,61,36,36,4,100,117,20,68,20,4,68,4]
theorem certificate_chunk_14 :
 checkRows ((matchings 4 [3,4,5,6,7,9,10,11]).map (fun E => [(0,2),(1,8)] ++ E)) codes_14 = true := by decide +kernel
#print axioms certificate_chunk_14
end Pool039Finite
```

### `CertificateChunk15.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_15 : List ℕ := [2,36,4,18,36,36,2,98,117,20,68,20,4,68,4,10,106,125,18,106,125,10,106,117,20,82,20,20,125,20,2,36,4,26,106,125,10,106,117,90,90,50,125,125,61,10,36,36,34,36,36,10,106,109,20,90,58,20,93,61,2,98,109,18,98,109,2,98,109,82,82,50,93,93,61,12,68,12,61,61,36,12,61,93,68,68,36,12,109,12,4,68,4,61,61,36,4,61,93,68,68,36,4,109,4]
theorem certificate_chunk_15 :
 checkRows ((matchings 4 [3,4,5,6,7,8,10,11]).map (fun E => [(0,2),(1,9)] ++ E)) codes_15 = true := by decide +kernel
#print axioms certificate_chunk_15
end Pool039Finite
```

### `CertificateChunk16.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_16 : List ℕ := [4,66,4,82,82,34,4,82,50,66,66,34,4,117,4,74,74,42,82,82,42,74,82,50,74,74,42,18,117,18,4,66,4,90,90,42,74,90,50,74,74,42,26,117,26,74,74,34,98,98,34,74,90,58,74,74,42,18,117,26,4,74,42,82,98,42,4,98,121,74,74,42,26,117,26,66,66,34,82,82,34,66,82,50,66,66,34,18,117,18,4,109,4,61,61,61,4,61,61,93,93,61,4,109,4]
theorem certificate_chunk_16 :
 checkRows ((matchings 4 [3,4,5,6,7,8,9,11]).map (fun E => [(0,2),(1,10)] ++ E)) codes_16 = true := by decide +kernel
#print axioms certificate_chunk_16
end Pool039Finite
```

### `CertificateChunk17.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_17 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,10,42,10,18,42,18,10,50,18,18,74,18,10,42,10,2,34,2,26,42,26,10,50,26,26,74,26,10,42,10,10,34,10,34,34,34,10,58,26,18,74,26,10,42,10,2,42,10,18,42,42,2,98,121,26,74,26,10,74,10,10,66,10,82,82,34,10,82,50,66,66,34,10,121,10,2,34,2,18,34,18,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_17 :
 checkRows ((matchings 4 [3,4,5,6,7,8,9,10]).map (fun E => [(0,2),(1,11)] ++ E)) codes_17 = true := by decide +kernel
#print axioms certificate_chunk_17
end Pool039Finite
```

### `CertificateChunk18.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_18 : List ℕ := [0,32,0,16,32,16,0,48,16,16,64,16,0,32,0,8,40,8,16,40,16,8,48,16,16,72,16,8,40,8,0,32,0,24,40,24,8,48,24,24,72,24,8,40,8,8,32,8,32,32,32,8,56,24,16,72,24,8,40,8,0,40,8,16,40,40,0,96,121,24,72,24,8,72,8,8,64,8,80,80,32,8,80,48,64,64,32,8,121,8,0,32,0,16,32,16,0,48,16,16,64,16,0,32,0]
theorem certificate_chunk_18 :
 checkRows ((matchings 4 [4,5,6,7,8,9,10,11]).map (fun E => [(0,3),(1,2)] ++ E)) codes_18 = true := by decide +kernel
#print axioms certificate_chunk_18
end Pool039Finite
```

### `CertificateChunk19.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_19 : List ℕ := [6,38,6,22,38,22,6,54,22,22,70,22,6,38,6,10,42,10,22,42,22,10,54,22,22,74,22,10,42,10,6,38,6,26,42,26,10,54,26,26,74,26,10,42,10,10,38,10,38,38,38,10,58,26,22,74,26,10,42,10,6,42,10,22,42,42,6,102,121,26,74,26,10,74,10,10,70,10,86,86,38,10,86,54,70,70,38,10,121,10,6,38,6,22,38,22,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_19 :
 checkRows ((matchings 4 [2,5,6,7,8,9,10,11]).map (fun E => [(0,3),(1,4)] ++ E)) codes_19 = true := by decide +kernel
#print axioms certificate_chunk_19
end Pool039Finite
```

### `CertificateChunk2.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_2 : List ℕ := [0,32,0,16,32,16,0,48,16,16,64,16,0,32,0,12,44,12,20,44,20,12,52,20,20,76,20,12,44,12,4,36,4,24,44,24,12,52,24,24,76,24,12,44,12,12,36,12,36,36,36,12,56,24,20,76,24,12,44,12,4,44,12,20,44,44,4,100,121,24,76,24,12,76,12,12,68,12,84,84,36,12,84,52,68,68,36,12,121,12,4,36,4,20,36,20,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_2 :
 checkRows ((matchings 4 [3,4,6,7,8,9,10,11]).map (fun E => [(0,1),(2,5)] ++ E)) codes_2 = true := by decide +kernel
#print axioms certificate_chunk_2
end Pool039Finite
```

### `CertificateChunk20.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_20 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,12,44,12,22,44,22,12,54,22,22,76,22,12,44,12,6,38,6,26,44,26,12,54,26,26,76,26,12,44,12,12,38,12,38,38,38,12,58,26,22,76,26,12,44,12,6,44,12,22,44,44,6,102,121,26,76,26,12,76,12,12,70,12,86,86,38,12,86,54,70,70,38,12,121,12,6,38,6,22,38,22,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_20 :
 checkRows ((matchings 4 [2,4,6,7,8,9,10,11]).map (fun E => [(0,3),(1,5)] ++ E)) codes_20 = true := by decide +kernel
#print axioms certificate_chunk_20
end Pool039Finite
```

### `CertificateChunk21.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_21 : List ℕ := [6,38,6,18,38,18,6,50,18,18,70,18,6,38,6,18,50,18,18,50,18,18,50,18,18,82,18,18,125,18,6,38,6,28,44,28,12,54,28,28,76,28,12,44,12,10,38,10,38,38,38,12,58,28,22,76,28,12,44,12,6,42,10,22,44,44,6,102,121,28,76,28,12,76,12,10,70,10,86,86,38,12,86,54,70,70,38,12,121,12,6,38,6,22,38,22,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_21 :
 checkRows ((matchings 4 [2,4,5,7,8,9,10,11]).map (fun E => [(0,3),(1,6)] ++ E)) codes_21 = true := by decide +kernel
#print axioms certificate_chunk_21
end Pool039Finite
```

### `CertificateChunk22.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_22 : List ℕ := [2,34,2,22,38,22,6,50,22,22,70,22,6,38,6,10,42,10,22,50,22,22,50,22,22,86,22,22,125,22,2,34,2,50,50,50,61,50,50,61,61,50,61,61,61,12,38,12,38,38,38,12,60,28,22,76,28,12,44,12,6,42,12,38,42,42,6,102,121,26,76,28,12,76,12,12,70,12,102,102,38,12,86,54,70,70,38,12,121,12,6,38,6,38,38,38,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_22 :
 checkRows ((matchings 4 [2,4,5,6,8,9,10,11]).map (fun E => [(0,3),(1,7)] ++ E)) codes_22 = true := by decide +kernel
#print axioms certificate_chunk_22
end Pool039Finite
```

### `CertificateChunk23.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_23 : List ℕ := [6,34,6,34,34,34,6,54,22,18,70,22,6,38,6,42,42,42,42,42,42,18,54,22,18,86,22,18,125,22,6,34,6,42,42,42,26,54,54,26,61,54,26,61,61,34,34,34,34,34,34,18,114,109,18,61,93,18,61,61,6,44,12,61,44,44,6,102,117,28,76,28,12,76,12,10,70,12,61,102,38,10,102,117,70,70,38,12,121,12,6,38,6,61,38,38,6,102,117,22,70,22,6,70,6]
theorem certificate_chunk_23 :
 checkRows ((matchings 4 [2,4,5,6,7,9,10,11]).map (fun E => [(0,3),(1,8)] ++ E)) codes_23 = true := by decide +kernel
#print axioms certificate_chunk_23
end Pool039Finite
```

### `CertificateChunk24.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_24 : List ℕ := [2,38,6,18,38,38,2,98,117,22,70,22,6,70,6,10,106,125,18,106,125,10,106,117,22,82,22,22,125,22,2,38,6,26,106,125,10,106,117,90,90,50,125,125,61,10,38,38,34,38,38,10,106,109,22,90,58,22,93,61,2,98,109,18,98,109,2,98,109,82,82,50,93,93,61,12,70,12,61,61,38,12,61,93,70,70,38,12,109,12,6,70,6,61,61,38,6,61,93,70,70,38,6,109,6]
theorem certificate_chunk_24 :
 checkRows ((matchings 4 [2,4,5,6,7,8,10,11]).map (fun E => [(0,3),(1,9)] ++ E)) codes_24 = true := by decide +kernel
#print axioms certificate_chunk_24
end Pool039Finite
```

### `CertificateChunk25.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_25 : List ℕ := [6,66,6,82,82,34,6,82,50,66,66,34,6,117,6,74,74,42,82,82,42,74,82,50,74,74,42,18,117,18,6,66,6,90,90,42,74,90,50,74,74,42,26,117,26,74,74,34,98,98,34,74,90,58,74,74,42,18,117,26,6,74,42,82,98,42,6,98,121,74,74,42,26,117,26,66,66,34,82,82,34,66,82,50,66,66,34,18,117,18,6,109,6,61,61,61,6,61,61,93,93,61,6,109,6]
theorem certificate_chunk_25 :
 checkRows ((matchings 4 [2,4,5,6,7,8,9,11]).map (fun E => [(0,3),(1,10)] ++ E)) codes_25 = true := by decide +kernel
#print axioms certificate_chunk_25
end Pool039Finite
```

### `CertificateChunk26.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_26 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,10,42,10,18,42,18,10,50,18,18,74,18,10,42,10,2,34,2,26,42,26,10,50,26,26,74,26,10,42,10,10,34,10,34,34,34,10,58,26,18,74,26,10,42,10,2,42,10,18,42,42,2,98,121,26,74,26,10,74,10,10,66,10,82,82,34,10,82,50,66,66,34,10,121,10,2,34,2,18,34,18,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_26 :
 checkRows ((matchings 4 [2,4,5,6,7,8,9,10]).map (fun E => [(0,3),(1,11)] ++ E)) codes_26 = true := by decide +kernel
#print axioms certificate_chunk_26
end Pool039Finite
```

### `CertificateChunk27.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_27 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,8,40,8,18,40,18,8,50,18,18,72,18,8,40,8,2,34,2,24,40,24,8,50,24,24,72,24,8,40,8,8,34,8,34,34,34,8,56,24,18,72,24,8,40,8,2,40,8,18,40,40,2,98,121,24,72,24,8,72,8,8,66,8,82,82,34,8,82,50,66,66,34,8,121,8,2,34,2,18,34,18,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_27 :
 checkRows ((matchings 4 [3,5,6,7,8,9,10,11]).map (fun E => [(0,4),(1,2)] ++ E)) codes_27 = true := by decide +kernel
#print axioms certificate_chunk_27
end Pool039Finite
```

### `CertificateChunk28.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_28 : List ℕ := [8,40,8,24,40,24,8,56,24,24,72,24,8,40,8,8,40,8,24,40,24,8,56,24,24,72,24,8,40,8,8,40,8,24,40,24,8,56,24,24,72,24,8,40,8,8,40,8,40,40,40,8,56,24,24,72,24,8,40,8,8,40,8,63,40,40,8,104,121,24,72,24,8,72,8,8,72,8,63,63,40,8,63,95,72,72,40,8,121,8,8,111,8,63,63,63,8,63,63,95,95,63,8,111,8]
theorem certificate_chunk_28 :
 checkRows ((matchings 4 [2,5,6,7,8,9,10,11]).map (fun E => [(0,4),(1,3)] ++ E)) codes_28 = true := by decide +kernel
#print axioms certificate_chunk_28
end Pool039Finite
```

### `CertificateChunk29.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_29 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,14,46,14,22,46,22,14,54,22,22,78,22,14,46,14,6,38,6,26,46,26,14,54,26,26,78,26,14,46,14,14,38,14,38,38,38,14,58,26,22,78,26,14,46,14,6,46,14,22,46,46,6,102,121,26,78,26,14,78,14,14,70,14,86,86,38,14,86,54,70,70,38,14,121,14,6,38,6,22,38,22,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_29 :
 checkRows ((matchings 4 [2,3,6,7,8,9,10,11]).map (fun E => [(0,4),(1,5)] ++ E)) codes_29 = true := by decide +kernel
#print axioms certificate_chunk_29
end Pool039Finite
```

### `CertificateChunk3.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_3 : List ℕ := [4,36,4,16,36,16,4,48,16,16,68,16,4,36,4,16,48,16,16,48,16,16,48,16,16,80,16,16,125,16,4,36,4,28,44,28,12,52,28,28,76,28,12,44,12,8,36,8,36,36,36,12,56,28,20,76,28,12,44,12,4,40,8,20,44,44,4,100,121,28,76,28,12,76,12,8,68,8,84,84,36,12,84,52,68,68,36,12,121,12,4,36,4,20,36,20,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_3 :
 checkRows ((matchings 4 [3,4,5,7,8,9,10,11]).map (fun E => [(0,1),(2,6)] ++ E)) codes_3 = true := by decide +kernel
#print axioms certificate_chunk_3
end Pool039Finite
```

### `CertificateChunk30.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_30 : List ℕ := [4,36,4,18,36,18,4,50,18,18,68,18,4,36,4,18,50,18,18,50,18,18,50,18,18,82,18,18,125,18,6,38,6,28,46,28,14,54,28,28,78,28,14,46,14,10,38,10,38,38,38,14,58,28,22,78,28,14,46,14,6,42,10,22,46,46,6,102,121,28,78,28,14,78,14,10,70,10,86,86,38,14,86,54,70,70,38,14,121,14,6,38,6,22,38,22,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_30 :
 checkRows ((matchings 4 [2,3,5,7,8,9,10,11]).map (fun E => [(0,4),(1,6)] ++ E)) codes_30 = true := by decide +kernel
#print axioms certificate_chunk_30
end Pool039Finite
```

### `CertificateChunk31.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_31 : List ℕ := [2,34,2,20,36,20,4,50,20,20,68,20,4,36,4,10,42,10,22,50,22,22,50,22,22,86,22,22,125,22,2,34,2,50,50,50,61,50,50,61,61,50,61,61,61,14,38,14,38,38,38,14,60,28,22,78,28,14,46,14,6,42,14,38,42,42,6,102,121,26,78,28,14,78,14,14,70,14,102,102,38,14,86,54,70,70,38,14,121,14,6,38,6,38,38,38,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_31 :
 checkRows ((matchings 4 [2,3,5,6,8,9,10,11]).map (fun E => [(0,4),(1,7)] ++ E)) codes_31 = true := by decide +kernel
#print axioms certificate_chunk_31
end Pool039Finite
```

### `CertificateChunk32.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_32 : List ℕ := [4,34,4,34,34,34,4,52,20,18,68,20,4,36,4,42,42,42,42,42,42,18,54,22,18,86,22,18,125,22,6,34,6,42,42,42,26,54,54,26,61,54,26,61,61,34,34,34,34,34,34,18,114,109,18,61,93,18,61,61,6,46,14,61,46,46,6,102,117,28,78,28,14,78,14,10,70,14,61,102,38,10,102,117,70,70,38,14,121,14,6,38,6,61,38,38,6,102,117,22,70,22,6,70,6]
theorem certificate_chunk_32 :
 checkRows ((matchings 4 [2,3,5,6,7,9,10,11]).map (fun E => [(0,4),(1,8)] ++ E)) codes_32 = true := by decide +kernel
#print axioms certificate_chunk_32
end Pool039Finite
```

### `CertificateChunk33.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_33 : List ℕ := [2,36,4,18,36,36,2,98,117,20,68,20,4,68,4,10,106,125,18,106,125,10,106,117,22,82,22,22,125,22,2,38,6,26,106,125,10,106,117,90,90,50,125,125,61,10,38,38,34,38,38,10,106,109,22,90,58,22,93,61,2,98,109,18,98,109,2,98,109,82,82,50,93,93,61,14,70,14,61,61,38,14,61,93,70,70,38,14,109,14,6,70,6,61,61,38,6,61,93,70,70,38,6,109,6]
theorem certificate_chunk_33 :
 checkRows ((matchings 4 [2,3,5,6,7,8,10,11]).map (fun E => [(0,4),(1,9)] ++ E)) codes_33 = true := by decide +kernel
#print axioms certificate_chunk_33
end Pool039Finite
```

### `CertificateChunk34.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_34 : List ℕ := [4,66,4,82,82,34,4,82,50,66,66,34,4,117,4,74,74,42,82,82,42,74,82,50,74,74,42,18,117,18,6,66,6,90,90,42,74,90,50,74,74,42,26,117,26,74,74,34,98,98,34,74,90,58,74,74,42,18,117,26,6,74,42,82,98,42,6,98,121,74,74,42,26,117,26,66,66,34,82,82,34,66,82,50,66,66,34,18,117,18,6,109,6,61,61,61,6,61,61,93,93,61,6,109,6]
theorem certificate_chunk_34 :
 checkRows ((matchings 4 [2,3,5,6,7,8,9,11]).map (fun E => [(0,4),(1,10)] ++ E)) codes_34 = true := by decide +kernel
#print axioms certificate_chunk_34
end Pool039Finite
```

### `CertificateChunk35.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_35 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,10,42,10,18,42,18,10,50,18,18,74,18,10,42,10,2,34,2,26,42,26,10,50,26,26,74,26,10,42,10,10,34,10,34,34,34,10,58,26,18,74,26,10,42,10,2,42,10,18,42,42,2,98,121,26,74,26,10,74,10,10,66,10,82,82,34,10,82,50,66,66,34,10,121,10,2,34,2,18,34,18,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_35 :
 checkRows ((matchings 4 [2,3,5,6,7,8,9,10]).map (fun E => [(0,4),(1,11)] ++ E)) codes_35 = true := by decide +kernel
#print axioms certificate_chunk_35
end Pool039Finite
```

### `CertificateChunk36.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_36 : List ℕ := [0,32,0,16,32,16,0,48,16,16,64,16,0,32,0,10,42,10,18,42,18,10,50,18,18,74,18,10,42,10,2,34,2,24,42,24,10,50,24,24,74,24,10,42,10,10,34,10,34,34,34,10,56,24,18,74,24,10,42,10,2,42,10,18,42,42,2,98,121,24,74,24,10,74,10,10,66,10,82,82,34,10,82,50,66,66,34,10,121,10,2,34,2,18,34,18,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_36 :
 checkRows ((matchings 4 [3,4,6,7,8,9,10,11]).map (fun E => [(0,5),(1,2)] ++ E)) codes_36 = true := by decide +kernel
#print axioms certificate_chunk_36
end Pool039Finite
```

### `CertificateChunk37.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_37 : List ℕ := [4,36,4,20,36,20,4,52,20,20,68,20,4,36,4,10,42,10,24,42,24,10,56,24,24,74,24,10,42,10,10,42,10,24,42,24,10,56,24,24,74,24,10,42,10,10,42,10,42,42,42,10,56,24,24,74,24,10,42,10,10,42,10,63,42,42,10,106,121,24,74,24,10,74,10,10,74,10,63,63,42,10,63,95,74,74,42,10,121,10,10,111,10,63,63,63,10,63,63,95,95,63,10,111,10]
theorem certificate_chunk_37 :
 checkRows ((matchings 4 [2,4,6,7,8,9,10,11]).map (fun E => [(0,5),(1,3)] ++ E)) codes_37 = true := by decide +kernel
#print axioms certificate_chunk_37
end Pool039Finite
```

### `CertificateChunk38.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_38 : List ℕ := [0,32,0,16,32,16,0,48,16,16,64,16,0,32,0,24,56,24,24,56,24,24,56,24,24,88,24,24,119,24,31,31,31,24,56,24,24,56,24,24,88,24,24,119,24,31,31,31,31,31,31,24,56,24,24,88,24,24,119,24,31,31,31,31,31,31,31,31,31,24,88,24,24,119,24,31,31,31,31,31,31,31,31,31,31,31,31,24,121,24,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31]
theorem certificate_chunk_38 :
 checkRows ((matchings 4 [2,3,6,7,8,9,10,11]).map (fun E => [(0,5),(1,4)] ++ E)) codes_38 = true := by decide +kernel
#print axioms certificate_chunk_38
end Pool039Finite
```

### `CertificateChunk39.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_39 : List ℕ := [6,38,6,18,38,18,6,50,18,18,70,18,6,38,6,18,50,18,18,50,18,18,50,18,18,82,18,18,123,18,6,38,6,30,46,30,14,54,30,30,78,30,14,46,14,10,38,10,38,38,38,14,58,30,22,78,30,14,46,14,6,42,10,22,46,46,6,102,121,30,78,30,14,78,14,10,70,10,86,86,38,14,86,54,70,70,38,14,121,14,6,38,6,22,38,22,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_39 :
 checkRows ((matchings 4 [2,3,4,7,8,9,10,11]).map (fun E => [(0,5),(1,6)] ++ E)) codes_39 = true := by decide +kernel
#print axioms certificate_chunk_39
end Pool039Finite
```

### `CertificateChunk4.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_4 : List ℕ := [0,32,0,20,36,20,4,48,20,20,68,20,4,36,4,8,40,8,20,48,20,20,48,20,20,84,20,20,125,20,0,32,0,48,48,48,61,48,48,61,61,48,61,61,61,12,36,12,36,36,36,12,60,28,20,76,28,12,44,12,4,40,12,36,40,40,4,100,121,24,76,28,12,76,12,12,68,12,100,100,36,12,84,52,68,68,36,12,121,12,4,36,4,36,36,36,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_4 :
 checkRows ((matchings 4 [3,4,5,6,8,9,10,11]).map (fun E => [(0,1),(2,7)] ++ E)) codes_4 = true := by decide +kernel
#print axioms certificate_chunk_4
end Pool039Finite
```

### `CertificateChunk40.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_40 : List ℕ := [2,34,2,20,38,20,6,50,20,20,70,20,6,38,6,18,50,18,20,50,20,20,50,20,20,84,20,20,123,20,2,34,2,50,50,50,61,50,50,61,61,50,61,61,61,12,38,12,38,38,38,14,60,30,22,78,30,14,46,14,6,42,12,38,42,42,6,102,121,26,78,30,14,78,14,12,70,12,102,102,38,14,86,54,70,70,38,14,121,14,6,38,6,38,38,38,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_40 :
 checkRows ((matchings 4 [2,3,4,6,8,9,10,11]).map (fun E => [(0,5),(1,7)] ++ E)) codes_40 = true := by decide +kernel
#print axioms certificate_chunk_40
end Pool039Finite
```

### `CertificateChunk41.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_41 : List ℕ := [6,34,6,34,34,34,6,52,20,18,70,20,6,38,6,50,50,50,50,50,50,18,52,20,18,84,20,18,123,20,6,34,6,42,42,42,26,54,54,26,61,54,26,61,61,34,34,34,34,34,34,18,114,109,18,61,93,18,61,61,6,44,12,61,46,46,6,102,117,30,78,30,14,78,14,10,70,12,61,102,38,10,102,117,70,70,38,14,121,14,6,38,6,61,38,38,6,102,117,22,70,22,6,70,6]
theorem certificate_chunk_41 :
 checkRows ((matchings 4 [2,3,4,6,7,9,10,11]).map (fun E => [(0,5),(1,8)] ++ E)) codes_41 = true := by decide +kernel
#print axioms certificate_chunk_41
end Pool039Finite
```

### `CertificateChunk42.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_42 : List ℕ := [2,38,6,18,38,38,2,98,117,20,70,20,6,70,6,18,114,125,18,114,125,18,114,117,20,82,20,20,123,20,2,38,6,26,106,125,10,106,117,90,90,50,125,125,61,10,38,38,34,38,38,10,106,109,22,90,58,22,93,61,2,98,109,18,98,109,2,98,109,82,82,50,93,93,61,12,70,12,61,61,38,14,61,93,70,70,38,14,109,14,6,70,6,61,61,38,6,61,93,70,70,38,6,109,6]
theorem certificate_chunk_42 :
 checkRows ((matchings 4 [2,3,4,6,7,8,10,11]).map (fun E => [(0,5),(1,9)] ++ E)) codes_42 = true := by decide +kernel
#print axioms certificate_chunk_42
end Pool039Finite
```

### `CertificateChunk43.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_43 : List ℕ := [6,66,6,82,82,34,6,82,50,66,66,34,6,117,6,82,82,50,82,82,50,82,82,50,82,82,50,18,117,18,6,66,6,90,90,42,74,90,50,74,74,42,26,117,26,74,74,34,98,98,34,74,90,58,74,74,42,18,117,26,6,74,42,82,98,42,6,98,121,74,74,42,26,117,26,66,66,34,82,82,34,66,82,50,66,66,34,18,117,18,6,109,6,61,61,61,6,61,61,93,93,61,6,109,6]
theorem certificate_chunk_43 :
 checkRows ((matchings 4 [2,3,4,6,7,8,9,11]).map (fun E => [(0,5),(1,10)] ++ E)) codes_43 = true := by decide +kernel
#print axioms certificate_chunk_43
end Pool039Finite
```

### `CertificateChunk44.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_44 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,18,50,18,18,50,18,18,50,18,18,82,18,18,123,18,2,34,2,26,42,26,10,50,26,26,74,26,10,42,10,10,34,10,34,34,34,10,58,26,18,74,26,10,42,10,2,42,10,18,42,42,2,98,121,26,74,26,10,74,10,10,66,10,82,82,34,10,82,50,66,66,34,10,121,10,2,34,2,18,34,18,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_44 :
 checkRows ((matchings 4 [2,3,4,6,7,8,9,10]).map (fun E => [(0,5),(1,11)] ++ E)) codes_44 = true := by decide +kernel
#print axioms certificate_chunk_44
end Pool039Finite
```

### `CertificateChunk45.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_45 : List ℕ := [2,34,2,16,34,16,2,48,16,16,66,16,2,34,2,16,48,16,16,48,16,16,48,16,16,80,16,16,123,16,2,34,2,26,42,26,10,50,26,26,74,26,10,42,10,8,34,8,34,34,34,10,56,26,18,74,26,10,42,10,2,40,8,18,42,42,2,98,121,26,74,26,10,74,10,8,66,8,82,82,34,10,82,50,66,66,34,10,121,10,2,34,2,18,34,18,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_45 :
 checkRows ((matchings 4 [3,4,5,7,8,9,10,11]).map (fun E => [(0,6),(1,2)] ++ E)) codes_45 = true := by decide +kernel
#print axioms certificate_chunk_45
end Pool039Finite
```

### `CertificateChunk46.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_46 : List ℕ := [20,52,20,20,52,20,20,52,20,20,84,20,20,127,20,20,52,20,20,52,20,20,52,20,20,84,20,20,123,20,8,40,8,26,42,26,10,56,26,26,74,26,10,42,10,8,40,8,42,42,42,10,56,26,26,74,26,10,42,10,8,40,8,63,42,42,10,106,121,26,74,26,10,74,10,8,72,8,63,63,42,10,63,95,74,74,42,10,121,10,8,111,8,63,63,63,10,63,63,95,95,63,10,111,10]
theorem certificate_chunk_46 :
 checkRows ((matchings 4 [2,4,5,7,8,9,10,11]).map (fun E => [(0,6),(1,3)] ++ E)) codes_46 = true := by decide +kernel
#print axioms certificate_chunk_46
end Pool039Finite
```

### `CertificateChunk47.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_47 : List ℕ := [2,34,2,16,34,16,2,48,16,16,66,16,2,34,2,20,52,20,20,52,20,20,52,20,20,84,20,20,119,20,12,44,12,26,56,26,26,56,26,26,90,26,26,119,26,12,44,12,31,31,31,26,56,26,26,90,26,26,119,26,12,44,12,31,31,31,31,31,31,26,90,26,26,119,26,12,76,12,31,31,31,31,31,31,31,31,31,26,121,26,12,111,12,31,31,31,31,31,31,31,31,31,31,31,31]
theorem certificate_chunk_47 :
 checkRows ((matchings 4 [2,3,5,7,8,9,10,11]).map (fun E => [(0,6),(1,4)] ++ E)) codes_47 = true := by decide +kernel
#print axioms certificate_chunk_47
end Pool039Finite
```

### `CertificateChunk48.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_48 : List ℕ := [16,48,16,16,48,16,16,48,16,16,80,16,16,119,16,16,48,16,16,48,16,16,48,16,16,80,16,16,119,16,8,40,8,56,56,56,55,56,56,55,55,56,55,55,55,8,40,8,31,31,31,47,56,56,47,55,56,47,55,55,8,40,8,31,31,31,31,31,31,47,47,56,47,47,55,8,72,8,31,31,31,31,31,31,31,31,31,47,47,47,8,111,8,31,31,31,31,31,31,31,31,31,31,31,31]
theorem certificate_chunk_48 :
 checkRows ((matchings 4 [2,3,4,7,8,9,10,11]).map (fun E => [(0,6),(1,5)] ++ E)) codes_48 = true := by decide +kernel
#print axioms certificate_chunk_48
end Pool039Finite
```

### `CertificateChunk49.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_49 : List ℕ := [2,34,2,22,38,22,6,50,22,22,70,22,6,38,6,31,31,31,22,50,22,22,50,22,22,86,22,22,123,22,2,34,2,50,50,50,59,50,50,59,59,50,59,59,59,14,38,14,38,38,38,14,62,30,22,78,30,14,46,14,6,42,14,38,42,42,6,102,121,26,78,30,14,78,14,14,70,14,102,102,38,14,86,54,70,70,38,14,121,14,6,38,6,38,38,38,6,54,22,22,70,22,6,38,6]
theorem certificate_chunk_49 :
 checkRows ((matchings 4 [2,3,4,5,8,9,10,11]).map (fun E => [(0,6),(1,7)] ++ E)) codes_49 = true := by decide +kernel
#print axioms certificate_chunk_49
end Pool039Finite
```

### `CertificateChunk5.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_5 : List ℕ := [4,32,4,32,32,32,4,52,20,16,68,20,4,36,4,40,40,40,40,40,40,16,52,20,16,84,20,16,125,20,4,32,4,40,40,40,24,52,52,24,61,52,24,61,61,32,32,32,32,32,32,16,112,109,16,61,93,16,61,61,4,44,12,61,44,44,4,100,117,28,76,28,12,76,12,8,68,12,61,100,36,8,100,117,68,68,36,12,121,12,4,36,4,61,36,36,4,100,117,20,68,20,4,68,4]
theorem certificate_chunk_5 :
 checkRows ((matchings 4 [3,4,5,6,7,9,10,11]).map (fun E => [(0,1),(2,8)] ++ E)) codes_5 = true := by decide +kernel
#print axioms certificate_chunk_5
end Pool039Finite
```

### `CertificateChunk50.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_50 : List ℕ := [4,34,4,34,34,34,6,52,22,18,70,22,6,38,6,31,31,31,50,50,50,18,52,22,18,86,22,18,123,22,4,34,4,50,50,50,59,52,52,59,59,52,59,59,59,34,34,34,34,34,34,18,114,109,18,61,93,18,61,61,6,44,14,61,44,44,6,102,117,28,78,30,14,78,14,10,70,14,61,102,38,10,102,117,70,70,38,14,121,14,6,38,6,61,38,38,6,102,117,22,70,22,6,70,6]
theorem certificate_chunk_50 :
 checkRows ((matchings 4 [2,3,4,5,7,9,10,11]).map (fun E => [(0,6),(1,8)] ++ E)) codes_50 = true := by decide +kernel
#print axioms certificate_chunk_50
end Pool039Finite
```

### `CertificateChunk51.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_51 : List ℕ := [2,36,4,18,38,38,2,98,117,22,70,22,6,70,6,31,31,31,18,114,125,18,114,117,22,82,22,22,123,22,2,36,4,50,114,125,59,114,117,59,59,50,59,59,59,10,38,38,34,38,38,10,106,109,22,90,58,22,93,61,2,98,109,34,98,109,2,98,109,82,82,50,93,93,61,14,70,14,61,61,38,14,61,93,70,70,38,14,109,14,6,70,6,61,61,38,6,61,93,70,70,38,6,109,6]
theorem certificate_chunk_51 :
 checkRows ((matchings 4 [2,3,4,5,7,8,10,11]).map (fun E => [(0,6),(1,9)] ++ E)) codes_51 = true := by decide +kernel
#print axioms certificate_chunk_51
end Pool039Finite
```

### `CertificateChunk52.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_52 : List ℕ := [4,66,4,82,82,34,6,82,50,66,66,34,6,117,6,31,31,31,82,82,50,82,82,50,82,82,50,18,117,18,4,66,4,114,114,50,59,114,50,59,59,50,59,59,59,74,74,34,98,98,34,74,90,58,74,74,42,18,117,26,6,74,42,98,98,42,6,98,121,74,74,42,26,117,26,66,66,34,98,98,34,66,82,50,66,66,34,18,117,18,6,109,6,61,61,61,6,61,61,93,93,61,6,109,6]
theorem certificate_chunk_52 :
 checkRows ((matchings 4 [2,3,4,5,7,8,9,11]).map (fun E => [(0,6),(1,10)] ++ E)) codes_52 = true := by decide +kernel
#print axioms certificate_chunk_52
end Pool039Finite
```

### `CertificateChunk53.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_53 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,31,31,31,18,50,18,18,50,18,18,82,18,18,123,18,2,34,2,50,50,50,59,50,50,59,59,50,59,59,59,10,34,10,34,34,34,10,58,26,18,74,26,10,42,10,2,42,10,34,42,42,2,98,121,26,74,26,10,74,10,10,66,10,98,98,34,10,82,50,66,66,34,10,121,10,2,34,2,34,34,34,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_53 :
 checkRows ((matchings 4 [2,3,4,5,7,8,9,10]).map (fun E => [(0,6),(1,11)] ++ E)) codes_53 = true := by decide +kernel
#print axioms certificate_chunk_53
end Pool039Finite
```

### `CertificateChunk54.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_54 : List ℕ := [0,32,0,18,34,18,2,48,18,18,66,18,2,34,2,8,40,8,18,48,18,18,48,18,18,82,18,18,123,18,0,32,0,48,48,48,59,48,48,59,59,48,59,59,59,10,34,10,34,34,34,10,58,26,18,74,26,10,42,10,2,40,10,34,40,40,2,98,121,24,74,26,10,74,10,10,66,10,98,98,34,10,82,50,66,66,34,10,121,10,2,34,2,34,34,34,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_54 :
 checkRows ((matchings 4 [3,4,5,6,8,9,10,11]).map (fun E => [(0,7),(1,2)] ++ E)) codes_54 = true := by decide +kernel
#print axioms certificate_chunk_54
end Pool039Finite
```

### `CertificateChunk55.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_55 : List ℕ := [4,36,4,52,52,52,63,52,52,63,63,52,63,63,63,8,40,8,52,52,52,63,52,52,63,63,52,63,63,63,4,36,4,52,52,52,59,52,52,59,59,52,59,59,59,10,40,10,40,40,40,10,58,26,24,74,26,10,42,10,10,40,10,63,40,40,10,106,121,24,74,26,10,74,10,10,74,10,63,63,40,10,63,95,74,74,42,10,121,10,10,111,10,63,63,63,10,63,63,95,95,63,10,111,10]
theorem certificate_chunk_55 :
 checkRows ((matchings 4 [2,4,5,6,8,9,10,11]).map (fun E => [(0,7),(1,3)] ++ E)) codes_55 = true := by decide +kernel
#print axioms certificate_chunk_55
end Pool039Finite
```

### `CertificateChunk56.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_56 : List ℕ := [0,32,0,18,34,18,2,48,18,18,66,18,2,34,2,12,44,12,52,52,52,63,52,52,63,63,52,63,63,63,4,36,4,52,52,52,59,52,52,59,59,52,59,59,59,44,44,44,44,44,44,24,58,26,24,90,26,24,119,26,63,44,44,63,44,44,31,31,31,24,90,26,24,119,26,63,63,44,63,63,44,31,31,31,31,31,31,24,121,26,63,63,63,63,63,63,31,31,31,31,31,31,31,31,31]
theorem certificate_chunk_56 :
 checkRows ((matchings 4 [2,3,5,6,8,9,10,11]).map (fun E => [(0,7),(1,4)] ++ E)) codes_56 = true := by decide +kernel
#print axioms certificate_chunk_56
end Pool039Finite
```

### `CertificateChunk57.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_57 : List ℕ := [4,36,4,18,48,18,18,48,18,18,82,18,18,119,18,16,48,16,18,48,18,18,48,18,18,82,18,18,119,18,4,36,4,52,52,52,55,52,52,55,55,52,55,55,55,10,40,10,44,44,44,28,58,58,28,55,58,28,55,55,10,40,10,47,44,44,31,31,31,28,47,58,28,47,55,10,74,10,47,47,44,31,31,31,31,31,31,28,47,47,10,111,10,47,47,47,31,31,31,31,31,31,31,31,31]
theorem certificate_chunk_57 :
 checkRows ((matchings 4 [2,3,4,6,8,9,10,11]).map (fun E => [(0,7),(1,5)] ++ E)) codes_57 = true := by decide +kernel
#print axioms certificate_chunk_57
end Pool039Finite
```

### `CertificateChunk58.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_58 : List ℕ := [0,32,0,48,48,48,55,48,48,55,55,48,55,55,55,8,40,8,48,48,48,55,48,48,55,55,48,55,55,55,0,32,0,48,48,48,55,48,48,55,55,48,55,55,55,40,40,40,40,40,40,24,120,103,24,55,87,24,55,55,47,40,40,47,40,40,31,31,31,24,47,79,24,47,79,47,47,40,47,47,40,31,31,31,31,31,31,24,47,47,47,47,47,47,47,47,31,31,31,31,31,31,31,31,31]
theorem certificate_chunk_58 :
 checkRows ((matchings 4 [2,3,4,5,8,9,10,11]).map (fun E => [(0,7),(1,6)] ++ E)) codes_58 = true := by decide +kernel
#print axioms certificate_chunk_58
end Pool039Finite
```

### `CertificateChunk59.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_59 : List ℕ := [6,34,6,34,34,34,6,54,22,18,70,22,6,38,6,31,31,31,31,31,31,18,54,22,18,86,22,18,123,22,6,34,6,31,31,31,47,54,54,47,59,54,47,59,59,34,34,34,34,34,34,18,114,107,18,59,91,18,59,59,6,46,14,55,46,46,6,102,115,30,78,30,14,78,14,10,70,14,55,102,38,10,102,115,70,70,38,14,121,14,6,38,6,55,38,38,6,102,115,22,70,22,6,70,6]
theorem certificate_chunk_59 :
 checkRows ((matchings 4 [2,3,4,5,6,9,10,11]).map (fun E => [(0,7),(1,8)] ++ E)) codes_59 = true := by decide +kernel
#print axioms certificate_chunk_59
end Pool039Finite
```

### `CertificateChunk6.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_6 : List ℕ := [0,36,4,16,36,36,0,96,117,20,68,20,4,68,4,8,104,125,16,104,125,8,104,117,20,80,20,20,125,20,0,36,4,24,104,125,8,104,117,88,88,48,125,125,61,8,36,36,32,36,36,8,104,109,20,88,56,20,93,61,0,96,109,16,96,109,0,96,109,80,80,48,93,93,61,12,68,12,61,61,36,12,61,93,68,68,36,12,109,12,4,68,4,61,61,36,4,61,93,68,68,36,4,109,4]
theorem certificate_chunk_6 :
 checkRows ((matchings 4 [3,4,5,6,7,8,10,11]).map (fun E => [(0,1),(2,9)] ++ E)) codes_6 = true := by decide +kernel
#print axioms certificate_chunk_6
end Pool039Finite
```

### `CertificateChunk60.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_60 : List ℕ := [2,36,6,34,36,36,2,98,117,20,70,22,6,70,6,31,31,31,31,31,31,18,114,117,20,82,22,20,123,22,2,36,6,31,31,31,47,114,117,47,59,50,47,59,59,34,36,36,34,36,36,18,114,107,20,59,91,20,59,59,2,98,109,55,98,109,2,98,115,82,82,50,93,93,61,12,70,14,55,61,38,12,61,115,70,70,38,14,109,14,6,70,6,55,61,38,6,61,115,70,70,38,6,109,6]
theorem certificate_chunk_60 :
 checkRows ((matchings 4 [2,3,4,5,6,8,10,11]).map (fun E => [(0,7),(1,9)] ++ E)) codes_60 = true := by decide +kernel
#print axioms certificate_chunk_60
end Pool039Finite
```

### `CertificateChunk61.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_61 : List ℕ := [6,66,6,98,98,34,6,82,50,66,66,34,6,117,6,31,31,31,31,31,31,82,82,50,82,82,50,18,117,18,6,66,6,31,31,31,47,114,50,47,59,50,47,59,59,98,98,34,98,98,34,82,114,107,82,59,91,18,59,59,6,74,42,55,98,42,6,98,115,74,74,42,26,117,26,66,66,34,55,98,34,66,98,115,66,66,34,18,117,18,6,109,6,55,61,61,6,61,115,93,93,61,6,109,6]
theorem certificate_chunk_61 :
 checkRows ((matchings 4 [2,3,4,5,6,8,9,11]).map (fun E => [(0,7),(1,10)] ++ E)) codes_61 = true := by decide +kernel
#print axioms certificate_chunk_61
end Pool039Finite
```

### `CertificateChunk62.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_62 : List ℕ := [2,34,2,34,34,34,2,50,18,18,66,18,2,34,2,31,31,31,31,31,31,18,50,18,18,82,18,18,123,18,2,34,2,31,31,31,47,50,50,47,59,50,47,59,59,34,34,34,34,34,34,18,114,107,18,59,91,18,59,59,2,42,10,55,42,42,2,98,115,26,74,26,10,74,10,10,66,10,55,98,34,10,98,115,66,66,34,10,121,10,2,34,2,55,34,34,2,98,115,18,66,18,2,66,2]
theorem certificate_chunk_62 :
 checkRows ((matchings 4 [2,3,4,5,6,8,9,10]).map (fun E => [(0,7),(1,11)] ++ E)) codes_62 = true := by decide +kernel
#print axioms certificate_chunk_62
end Pool039Finite
```

### `CertificateChunk63.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_63 : List ℕ := [2,32,2,32,32,32,2,50,18,16,66,18,2,34,2,40,40,40,40,40,40,16,50,18,16,82,18,16,123,18,2,32,2,40,40,40,24,50,50,24,59,50,24,59,59,32,32,32,32,32,32,16,112,107,16,59,91,16,59,59,2,42,10,59,42,42,2,98,115,26,74,26,10,74,10,8,66,10,59,98,34,8,98,115,66,66,34,10,121,10,2,34,2,59,34,34,2,98,115,18,66,18,2,66,2]
theorem certificate_chunk_63 :
 checkRows ((matchings 4 [3,4,5,6,7,9,10,11]).map (fun E => [(0,8),(1,2)] ++ E)) codes_63 = true := by decide +kernel
#print axioms certificate_chunk_63
end Pool039Finite
```

### `CertificateChunk64.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_64 : List ℕ := [36,36,36,36,36,36,20,116,111,20,63,95,20,63,63,40,40,40,40,40,40,20,116,111,20,63,95,20,63,63,36,36,36,40,40,40,24,116,111,24,59,95,24,59,59,36,36,36,36,36,36,20,116,107,20,59,91,20,59,59,8,42,10,59,42,42,8,104,115,26,74,26,10,74,10,8,74,10,59,63,42,8,63,115,74,74,42,10,121,10,8,111,10,59,63,63,8,63,115,95,95,63,10,111,10]
theorem certificate_chunk_64 :
 checkRows ((matchings 4 [2,4,5,6,7,9,10,11]).map (fun E => [(0,8),(1,3)] ++ E)) codes_64 = true := by decide +kernel
#print axioms certificate_chunk_64
end Pool039Finite
```

### `CertificateChunk65.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_65 : List ℕ := [2,32,2,32,32,32,2,50,18,16,66,18,2,34,2,44,44,44,44,44,44,20,116,111,20,63,95,20,63,63,36,36,36,44,44,44,24,116,111,24,59,95,24,59,59,36,36,36,36,36,36,20,116,107,20,59,91,20,59,59,12,108,119,59,108,119,12,108,115,26,88,26,26,119,26,12,63,95,59,63,95,12,63,115,31,31,31,26,121,26,12,63,63,59,63,63,12,63,115,31,31,31,31,31,31]
theorem certificate_chunk_65 :
 checkRows ((matchings 4 [2,3,5,6,7,9,10,11]).map (fun E => [(0,8),(1,4)] ++ E)) codes_65 = true := by decide +kernel
#print axioms certificate_chunk_65
end Pool039Finite
```

### `CertificateChunk66.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_66 : List ℕ := [36,36,36,36,36,36,16,50,18,16,82,18,16,119,18,48,48,48,48,48,48,16,50,18,16,82,18,16,119,18,36,36,36,44,44,44,28,116,111,28,55,95,28,55,55,36,36,36,36,36,36,20,116,107,20,55,91,20,55,55,8,42,10,59,108,119,12,108,115,92,92,56,119,119,55,8,74,10,59,47,95,12,47,115,31,31,31,111,121,47,8,111,10,59,47,47,12,47,47,31,31,31,31,31,31]
theorem certificate_chunk_66 :
 checkRows ((matchings 4 [2,3,4,6,7,9,10,11]).map (fun E => [(0,8),(1,5)] ++ E)) codes_66 = true := by decide +kernel
#print axioms certificate_chunk_66
end Pool039Finite
```

### `CertificateChunk67.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_67 : List ℕ := [2,32,2,36,36,36,20,50,50,20,55,50,20,55,55,40,40,40,48,48,48,20,50,50,20,55,50,20,55,55,2,32,2,48,48,48,61,50,50,61,55,50,61,55,55,36,36,36,36,36,36,20,116,103,20,55,87,20,55,55,12,42,42,59,42,42,12,108,103,26,92,60,26,87,55,12,47,42,59,47,42,12,47,79,31,31,31,26,79,47,12,47,47,59,47,47,12,47,47,31,31,31,31,31,31]
theorem certificate_chunk_67 :
 checkRows ((matchings 4 [2,3,4,5,7,9,10,11]).map (fun E => [(0,8),(1,6)] ++ E)) codes_67 = true := by decide +kernel
#print axioms certificate_chunk_67
end Pool039Finite
```

### `CertificateChunk68.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_68 : List ℕ := [32,32,32,32,32,32,16,112,103,16,55,87,16,55,55,40,40,40,40,40,40,16,112,103,16,55,87,16,55,55,32,32,32,40,40,40,24,112,103,24,55,87,24,55,55,32,32,32,32,32,32,16,112,103,16,55,87,16,55,55,8,104,103,59,104,103,8,104,103,88,88,56,87,87,55,8,47,79,59,47,79,8,47,79,31,31,31,79,79,47,8,47,47,59,47,47,8,47,47,31,31,31,31,31,31]
theorem certificate_chunk_68 :
 checkRows ((matchings 4 [2,3,4,5,6,9,10,11]).map (fun E => [(0,8),(1,7)] ++ E)) codes_68 = true := by decide +kernel
#print axioms certificate_chunk_68
end Pool039Finite
```

### `CertificateChunk69.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_69 : List ℕ := [2,38,6,55,38,38,2,98,115,22,70,22,6,70,6,31,31,31,31,31,31,31,31,31,22,82,22,22,123,22,2,38,6,31,31,31,31,31,31,47,47,50,47,47,59,47,38,38,47,38,38,31,31,31,22,47,79,22,47,79,2,98,107,55,98,107,2,98,107,82,82,50,91,91,59,14,70,14,55,55,38,14,55,87,70,70,38,14,103,14,6,70,6,55,55,38,6,55,87,70,70,38,6,103,6]
theorem certificate_chunk_69 :
 checkRows ((matchings 4 [2,3,4,5,6,7,10,11]).map (fun E => [(0,8),(1,9)] ++ E)) codes_69 = true := by decide +kernel
#print axioms certificate_chunk_69
end Pool039Finite
```

### `CertificateChunk7.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_7 : List ℕ := [4,64,4,80,80,32,4,80,48,64,64,32,4,117,4,72,72,40,80,80,40,72,80,48,72,72,40,16,117,16,4,64,4,88,88,40,72,88,48,72,72,40,24,117,24,72,72,32,96,96,32,72,88,56,72,72,40,16,117,24,4,72,40,80,96,40,4,96,121,72,72,40,24,117,24,64,64,32,80,80,32,64,80,48,64,64,32,16,117,16,4,109,4,61,61,61,4,61,61,93,93,61,4,109,4]
theorem certificate_chunk_7 :
 checkRows ((matchings 4 [3,4,5,6,7,8,9,11]).map (fun E => [(0,1),(2,10)] ++ E)) codes_7 = true := by decide +kernel
#print axioms certificate_chunk_7
end Pool039Finite
```

### `CertificateChunk70.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_70 : List ℕ := [4,66,6,55,98,34,4,98,115,66,66,34,6,117,6,31,31,31,31,31,31,31,31,31,82,82,50,18,117,18,4,66,6,31,31,31,31,31,31,47,47,50,47,47,59,47,98,34,47,98,34,31,31,31,82,47,79,18,47,79,4,98,107,55,98,107,4,98,107,82,82,50,91,91,59,66,66,34,55,55,34,66,55,87,66,66,34,18,103,18,6,109,6,55,55,61,6,55,87,93,93,61,6,103,6]
theorem certificate_chunk_70 :
 checkRows ((matchings 4 [2,3,4,5,6,7,9,11]).map (fun E => [(0,8),(1,10)] ++ E)) codes_70 = true := by decide +kernel
#print axioms certificate_chunk_70
end Pool039Finite
```

### `CertificateChunk71.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_71 : List ℕ := [2,34,2,55,34,34,2,98,115,18,66,18,2,66,2,31,31,31,31,31,31,31,31,31,18,82,18,18,123,18,2,34,2,31,31,31,31,31,31,47,47,50,47,47,59,47,34,34,47,34,34,31,31,31,18,47,79,18,47,79,2,98,107,55,98,107,2,98,107,82,82,50,91,91,59,10,66,10,55,55,34,10,55,87,66,66,34,10,103,10,2,66,2,55,55,34,2,55,87,66,66,34,2,103,2]
theorem certificate_chunk_71 :
 checkRows ((matchings 4 [2,3,4,5,6,7,9,10]).map (fun E => [(0,8),(1,11)] ++ E)) codes_71 = true := by decide +kernel
#print axioms certificate_chunk_71
end Pool039Finite
```

### `CertificateChunk72.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_72 : List ℕ := [0,34,2,16,34,34,0,96,115,18,66,18,2,66,2,8,104,123,16,104,123,8,104,115,18,80,18,18,123,18,0,34,2,24,104,123,8,104,115,88,88,48,123,123,59,8,34,34,32,34,34,8,104,107,18,88,56,18,91,59,0,96,107,16,96,107,0,96,107,80,80,48,91,91,59,10,66,10,59,59,34,10,59,91,66,66,34,10,107,10,2,66,2,59,59,34,2,59,91,66,66,34,2,107,2]
theorem certificate_chunk_72 :
 checkRows ((matchings 4 [3,4,5,6,7,8,10,11]).map (fun E => [(0,9),(1,2)] ++ E)) codes_72 = true := by decide +kernel
#print axioms certificate_chunk_72
end Pool039Finite
```

### `CertificateChunk73.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_73 : List ℕ := [4,100,111,20,100,111,4,100,115,84,84,52,95,95,63,8,104,111,20,104,111,8,104,115,84,84,52,95,95,63,4,100,111,24,104,111,8,104,115,88,88,52,95,95,59,8,100,111,36,100,111,8,104,107,84,88,56,95,91,59,4,100,107,20,100,107,4,100,107,84,84,52,91,91,59,10,72,10,59,59,40,10,59,91,72,72,40,10,107,10,10,111,10,59,59,63,10,59,91,95,95,63,10,107,10]
theorem certificate_chunk_73 :
 checkRows ((matchings 4 [2,4,5,6,7,8,10,11]).map (fun E => [(0,9),(1,3)] ++ E)) codes_73 = true := by decide +kernel
#print axioms certificate_chunk_73
end Pool039Finite
```

### `CertificateChunk74.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_74 : List ℕ := [0,34,2,16,34,34,0,96,115,18,66,18,2,66,2,12,108,111,20,108,111,12,108,115,84,84,52,95,95,63,4,100,111,24,108,111,12,108,115,88,88,52,95,95,59,12,100,111,36,100,111,12,108,107,84,88,56,95,91,59,4,100,107,20,100,107,4,100,107,84,84,52,91,91,59,76,76,44,59,59,44,76,59,91,76,76,44,24,107,24,95,95,63,59,59,63,95,59,91,95,95,63,31,31,31]
theorem certificate_chunk_74 :
 checkRows ((matchings 4 [2,3,5,6,7,8,10,11]).map (fun E => [(0,9),(1,4)] ++ E)) codes_74 = true := by decide +kernel
#print axioms certificate_chunk_74
end Pool039Finite
```

### `CertificateChunk75.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_75 : List ℕ := [4,100,119,16,100,119,4,100,115,18,80,18,18,119,18,16,112,119,16,112,119,16,112,115,18,80,18,18,119,18,4,100,111,28,108,111,12,108,115,92,92,52,95,95,55,8,100,111,36,100,111,12,108,107,84,92,56,95,91,55,4,100,107,20,100,107,4,100,107,84,84,52,91,91,55,10,72,10,59,59,44,76,59,91,76,76,44,28,107,28,10,111,10,59,59,47,95,59,47,95,95,47,31,31,31]
theorem certificate_chunk_75 :
 checkRows ((matchings 4 [2,3,4,6,7,8,10,11]).map (fun E => [(0,9),(1,5)] ++ E)) codes_75 = true := by decide +kernel
#print axioms certificate_chunk_75
end Pool039Finite
```

### `CertificateChunk76.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_76 : List ℕ := [0,34,2,20,100,119,4,100,115,84,84,48,119,119,55,8,104,123,20,112,119,20,112,115,84,84,48,119,119,55,0,34,2,48,112,119,61,112,115,61,61,48,61,61,55,12,100,111,36,100,111,12,108,103,84,92,60,95,87,55,4,100,107,36,100,107,4,100,103,84,84,52,91,87,55,76,76,40,59,59,40,76,59,91,76,76,44,24,107,28,111,111,47,59,59,47,95,79,47,95,79,47,31,31,31]
theorem certificate_chunk_76 :
 checkRows ((matchings 4 [2,3,4,5,7,8,10,11]).map (fun E => [(0,9),(1,6)] ++ E)) codes_76 = true := by decide +kernel
#print axioms certificate_chunk_76
end Pool039Finite
```

### `CertificateChunk77.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_77 : List ℕ := [4,34,34,32,34,34,4,100,103,18,84,52,18,87,55,40,104,123,40,104,123,16,112,103,18,84,52,18,87,55,4,34,34,40,104,123,24,112,103,88,61,52,123,87,55,32,34,34,32,34,34,16,112,103,18,61,93,18,87,55,4,100,103,61,100,103,4,100,103,84,84,52,87,87,55,10,76,44,59,59,44,10,59,91,76,76,44,28,107,28,10,79,47,59,79,47,10,79,47,79,79,47,31,31,31]
theorem certificate_chunk_77 :
 checkRows ((matchings 4 [2,3,4,5,6,8,10,11]).map (fun E => [(0,9),(1,7)] ++ E)) codes_77 = true := by decide +kernel
#print axioms certificate_chunk_77
end Pool039Finite
```

### `CertificateChunk78.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_78 : List ℕ := [0,96,103,16,96,103,0,96,103,80,80,48,87,87,55,8,104,103,16,104,103,8,104,103,80,80,48,87,87,55,0,96,103,24,104,103,8,104,103,88,88,48,87,87,55,8,96,103,32,96,103,8,104,103,80,88,56,87,87,55,0,96,103,16,96,103,0,96,103,80,80,48,87,87,55,72,72,40,59,59,40,72,59,91,72,72,40,24,107,24,79,79,47,79,79,47,79,79,47,79,79,47,31,31,31]
theorem certificate_chunk_78 :
 checkRows ((matchings 4 [2,3,4,5,6,7,10,11]).map (fun E => [(0,9),(1,8)] ++ E)) codes_78 = true := by decide +kernel
#print axioms certificate_chunk_78
end Pool039Finite
```

### `CertificateChunk79.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_79 : List ℕ := [6,66,6,55,55,34,6,55,87,66,66,34,6,103,6,31,31,31,31,31,31,31,31,31,31,31,31,18,103,18,6,66,6,31,31,31,31,31,31,31,31,31,47,47,47,47,47,34,47,47,34,31,31,31,31,31,31,18,47,47,6,47,79,55,47,79,6,47,79,31,31,31,79,79,47,66,66,34,55,55,34,66,55,87,66,66,34,18,103,18,6,103,6,55,55,55,6,55,55,87,87,55,6,103,6]
theorem certificate_chunk_79 :
 checkRows ((matchings 4 [2,3,4,5,6,7,8,11]).map (fun E => [(0,9),(1,10)] ++ E)) codes_79 = true := by decide +kernel
#print axioms certificate_chunk_79
end Pool039Finite
```

### `CertificateChunk8.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_8 : List ℕ := [0,32,0,16,32,16,0,48,16,16,64,16,0,32,0,8,40,8,16,40,16,8,48,16,16,72,16,8,40,8,0,32,0,24,40,24,8,48,24,24,72,24,8,40,8,8,32,8,32,32,32,8,56,24,16,72,24,8,40,8,0,40,8,16,40,40,0,96,121,24,72,24,8,72,8,8,64,8,80,80,32,8,80,48,64,64,32,8,121,8,0,32,0,16,32,16,0,48,16,16,64,16,0,32,0]
theorem certificate_chunk_8 :
 checkRows ((matchings 4 [3,4,5,6,7,8,9,10]).map (fun E => [(0,1),(2,11)] ++ E)) codes_8 = true := by decide +kernel
#print axioms certificate_chunk_8
end Pool039Finite
```

### `CertificateChunk80.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_80 : List ℕ := [2,66,2,55,55,34,2,55,87,66,66,34,2,103,2,31,31,31,31,31,31,31,31,31,31,31,31,18,103,18,2,66,2,31,31,31,31,31,31,31,31,31,47,47,47,47,47,34,47,47,34,31,31,31,31,31,31,18,47,47,2,47,79,55,47,79,2,47,79,31,31,31,79,79,47,66,66,34,55,55,34,66,55,87,66,66,34,18,103,18,2,103,2,55,55,55,2,55,55,87,87,55,2,103,2]
theorem certificate_chunk_80 :
 checkRows ((matchings 4 [2,3,4,5,6,7,8,10]).map (fun E => [(0,9),(1,11)] ++ E)) codes_80 = true := by decide +kernel
#print axioms certificate_chunk_80
end Pool039Finite
```

### `CertificateChunk81.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_81 : List ℕ := [2,64,2,80,80,32,2,80,48,64,64,32,2,115,2,72,72,40,80,80,40,72,80,48,72,72,40,16,115,16,2,64,2,88,88,40,72,88,48,72,72,40,24,115,24,72,72,32,96,96,32,72,88,56,72,72,40,16,115,24,2,72,40,80,96,40,2,96,121,72,72,40,24,115,24,64,64,32,80,80,32,64,80,48,64,64,32,16,115,16,2,107,2,59,59,59,2,59,59,91,91,59,2,107,2]
theorem certificate_chunk_81 :
 checkRows ((matchings 4 [3,4,5,6,7,8,9,11]).map (fun E => [(0,10),(1,2)] ++ E)) codes_81 = true := by decide +kernel
#print axioms certificate_chunk_81
end Pool039Finite
```

### `CertificateChunk82.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_82 : List ℕ := [68,68,36,84,84,36,68,84,52,68,68,36,20,115,20,72,72,40,84,84,40,72,84,52,72,72,40,20,115,20,68,68,36,88,88,40,72,88,52,72,72,40,24,115,24,72,72,36,100,100,36,72,88,56,72,72,40,20,115,24,68,72,40,84,100,40,68,100,121,72,72,40,24,115,24,68,68,36,84,84,36,68,84,52,68,68,36,20,115,20,8,107,8,59,59,59,8,59,59,91,91,59,8,107,8]
theorem certificate_chunk_82 :
 checkRows ((matchings 4 [2,4,5,6,7,8,9,11]).map (fun E => [(0,10),(1,3)] ++ E)) codes_82 = true := by decide +kernel
#print axioms certificate_chunk_82
end Pool039Finite
```

### `CertificateChunk83.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_83 : List ℕ := [2,64,2,80,80,32,2,80,48,64,64,32,2,115,2,76,76,44,84,84,44,76,84,52,76,76,44,20,115,20,68,68,36,88,88,44,76,88,52,76,76,44,24,115,24,76,76,36,100,100,36,76,88,56,76,76,44,20,115,24,68,76,44,84,100,44,68,100,121,76,76,44,24,115,24,68,68,36,84,84,36,68,84,52,68,68,36,20,115,20,12,107,12,59,59,59,12,59,59,91,91,59,12,107,12]
theorem certificate_chunk_83 :
 checkRows ((matchings 4 [2,3,5,6,7,8,9,11]).map (fun E => [(0,10),(1,4)] ++ E)) codes_83 = true := by decide +kernel
#print axioms certificate_chunk_83
end Pool039Finite
```

### `CertificateChunk84.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_84 : List ℕ := [68,68,36,80,80,36,68,80,48,68,68,36,16,115,16,80,80,48,80,80,48,80,80,48,80,80,48,16,115,16,68,68,36,92,92,44,76,92,52,76,76,44,28,115,28,72,72,36,100,100,36,76,92,56,76,76,44,20,115,28,68,72,40,84,100,44,68,100,121,76,76,44,28,115,28,68,68,36,84,84,36,68,84,52,68,68,36,20,115,20,8,107,8,59,59,59,12,59,59,91,91,59,12,107,12]
theorem certificate_chunk_84 :
 checkRows ((matchings 4 [2,3,4,6,7,8,9,11]).map (fun E => [(0,10),(1,5)] ++ E)) codes_84 = true := by decide +kernel
#print axioms certificate_chunk_84
end Pool039Finite
```

### `CertificateChunk85.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_85 : List ℕ := [2,64,2,84,84,36,68,84,48,68,68,36,20,115,20,72,72,40,84,84,48,84,84,48,84,84,48,20,115,20,2,64,2,112,112,48,61,112,48,61,61,48,61,115,61,76,76,36,100,100,36,76,92,60,76,76,44,20,115,28,68,76,40,100,100,40,68,100,121,76,76,44,24,115,28,68,68,36,100,100,36,68,84,52,68,68,36,20,115,20,12,107,12,59,59,59,12,59,59,91,91,59,12,107,12]
theorem certificate_chunk_85 :
 checkRows ((matchings 4 [2,3,4,5,7,8,9,11]).map (fun E => [(0,10),(1,6)] ++ E)) codes_85 = true := by decide +kernel
#print axioms certificate_chunk_85
end Pool039Finite
```

### `CertificateChunk86.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_86 : List ℕ := [68,68,32,96,96,32,68,84,52,68,68,36,16,115,20,104,104,40,104,104,40,80,84,52,80,84,52,16,115,20,68,68,32,104,104,40,88,112,52,88,61,52,24,115,61,96,96,32,96,96,32,80,112,109,80,61,93,16,115,61,68,76,44,61,100,44,68,100,117,76,76,44,28,115,28,68,68,36,61,100,36,68,100,117,68,68,36,20,115,20,8,107,12,59,59,59,8,59,59,91,91,59,12,107,12]
theorem certificate_chunk_86 :
 checkRows ((matchings 4 [2,3,4,5,6,8,9,11]).map (fun E => [(0,10),(1,7)] ++ E)) codes_86 = true := by decide +kernel
#print axioms certificate_chunk_86
end Pool039Finite
```

### `CertificateChunk87.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_87 : List ℕ := [2,68,36,80,96,36,2,96,117,68,68,36,20,115,20,72,104,125,80,104,125,72,104,117,80,80,48,20,115,20,2,68,36,88,104,125,72,104,117,88,88,48,125,115,61,72,96,36,96,96,36,72,104,109,80,88,56,20,115,61,2,96,109,80,96,109,2,96,109,80,80,48,93,115,61,68,68,36,61,61,36,68,61,93,68,68,36,20,115,20,12,107,12,59,59,59,12,59,59,91,91,59,12,107,12]
theorem certificate_chunk_87 :
 checkRows ((matchings 4 [2,3,4,5,6,7,9,11]).map (fun E => [(0,10),(1,8)] ++ E)) codes_87 = true := by decide +kernel
#print axioms certificate_chunk_87
end Pool039Finite
```

### `CertificateChunk88.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_88 : List ℕ := [64,64,32,80,80,32,64,80,48,64,64,32,16,115,16,72,72,40,80,80,40,72,80,48,72,72,40,16,115,16,64,64,32,88,88,40,72,88,48,72,72,40,24,115,24,72,72,32,96,96,32,72,88,56,72,72,40,16,115,24,64,72,40,80,96,40,64,96,121,72,72,40,24,115,24,64,64,32,80,80,32,64,80,48,64,64,32,16,115,16,8,107,8,59,59,59,8,59,59,91,91,59,8,107,8]
theorem certificate_chunk_88 :
 checkRows ((matchings 4 [2,3,4,5,6,7,8,11]).map (fun E => [(0,10),(1,9)] ++ E)) codes_88 = true := by decide +kernel
#print axioms certificate_chunk_88
end Pool039Finite
```

### `CertificateChunk89.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_89 : List ℕ := [2,103,2,55,55,55,2,55,55,87,87,55,2,103,2,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,2,103,2,31,31,31,31,31,31,31,31,31,31,31,31,47,47,47,47,47,47,31,31,31,31,31,31,31,31,31,2,47,47,55,47,47,2,47,47,31,31,31,31,31,31,79,79,47,79,79,47,79,79,47,79,79,47,31,31,31,2,103,2,55,55,55,2,55,55,87,87,55,2,103,2]
theorem certificate_chunk_89 :
 checkRows ((matchings 4 [2,3,4,5,6,7,8,9]).map (fun E => [(0,10),(1,11)] ++ E)) codes_89 = true := by decide +kernel
#print axioms certificate_chunk_89
end Pool039Finite
```

### `CertificateChunk9.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_9 : List ℕ := [2,34,2,18,34,18,2,50,18,18,66,18,2,34,2,10,42,10,18,42,18,10,50,18,18,74,18,10,42,10,2,34,2,26,42,26,10,50,26,26,74,26,10,42,10,10,34,10,34,34,34,10,58,26,18,74,26,10,42,10,2,42,10,18,42,42,2,98,121,26,74,26,10,74,10,10,66,10,82,82,34,10,82,50,66,66,34,10,121,10,2,34,2,18,34,18,2,50,18,18,66,18,2,34,2]
theorem certificate_chunk_9 :
 checkRows ((matchings 4 [4,5,6,7,8,9,10,11]).map (fun E => [(0,2),(1,3)] ++ E)) codes_9 = true := by decide +kernel
#print axioms certificate_chunk_9
end Pool039Finite
```

### `CertificateChunk90.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_90 : List ℕ := [0,32,0,16,32,16,0,48,16,16,64,16,0,32,0,8,40,8,16,40,16,8,48,16,16,72,16,8,40,8,0,32,0,24,40,24,8,48,24,24,72,24,8,40,8,8,32,8,32,32,32,8,56,24,16,72,24,8,40,8,0,40,8,16,40,40,0,96,121,24,72,24,8,72,8,8,64,8,80,80,32,8,80,48,64,64,32,8,121,8,0,32,0,16,32,16,0,48,16,16,64,16,0,32,0]
theorem certificate_chunk_90 :
 checkRows ((matchings 4 [3,4,5,6,7,8,9,10]).map (fun E => [(0,11),(1,2)] ++ E)) codes_90 = true := by decide +kernel
#print axioms certificate_chunk_90
end Pool039Finite
```

### `CertificateChunk91.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_91 : List ℕ := [4,36,4,20,36,20,4,52,20,20,68,20,4,36,4,8,40,8,20,40,20,8,52,20,20,72,20,8,40,8,4,36,4,24,40,24,8,52,24,24,72,24,8,40,8,8,36,8,36,36,36,8,56,24,20,72,24,8,40,8,4,40,8,20,40,40,4,100,121,24,72,24,8,72,8,8,68,8,84,84,36,8,84,52,68,68,36,8,121,8,4,36,4,20,36,20,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_91 :
 checkRows ((matchings 4 [2,4,5,6,7,8,9,10]).map (fun E => [(0,11),(1,3)] ++ E)) codes_91 = true := by decide +kernel
#print axioms certificate_chunk_91
end Pool039Finite
```

### `CertificateChunk92.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_92 : List ℕ := [0,32,0,16,32,16,0,48,16,16,64,16,0,32,0,12,44,12,20,44,20,12,52,20,20,76,20,12,44,12,4,36,4,24,44,24,12,52,24,24,76,24,12,44,12,12,36,12,36,36,36,12,56,24,20,76,24,12,44,12,4,44,12,20,44,44,4,100,121,24,76,24,12,76,12,12,68,12,84,84,36,12,84,52,68,68,36,12,121,12,4,36,4,20,36,20,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_92 :
 checkRows ((matchings 4 [2,3,5,6,7,8,9,10]).map (fun E => [(0,11),(1,4)] ++ E)) codes_92 = true := by decide +kernel
#print axioms certificate_chunk_92
end Pool039Finite
```

### `CertificateChunk93.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_93 : List ℕ := [4,36,4,16,36,16,4,48,16,16,68,16,4,36,4,16,48,16,16,48,16,16,48,16,16,80,16,16,125,16,4,36,4,28,44,28,12,52,28,28,76,28,12,44,12,8,36,8,36,36,36,12,56,28,20,76,28,12,44,12,4,40,8,20,44,44,4,100,121,28,76,28,12,76,12,8,68,8,84,84,36,12,84,52,68,68,36,12,121,12,4,36,4,20,36,20,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_93 :
 checkRows ((matchings 4 [2,3,4,6,7,8,9,10]).map (fun E => [(0,11),(1,5)] ++ E)) codes_93 = true := by decide +kernel
#print axioms certificate_chunk_93
end Pool039Finite
```

### `CertificateChunk94.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_94 : List ℕ := [0,32,0,20,36,20,4,48,20,20,68,20,4,36,4,8,40,8,20,48,20,20,48,20,20,84,20,20,125,20,0,32,0,48,48,48,61,48,48,61,61,48,61,61,61,12,36,12,36,36,36,12,60,28,20,76,28,12,44,12,4,40,12,36,40,40,4,100,121,24,76,28,12,76,12,12,68,12,100,100,36,12,84,52,68,68,36,12,121,12,4,36,4,36,36,36,4,52,20,20,68,20,4,36,4]
theorem certificate_chunk_94 :
 checkRows ((matchings 4 [2,3,4,5,7,8,9,10]).map (fun E => [(0,11),(1,6)] ++ E)) codes_94 = true := by decide +kernel
#print axioms certificate_chunk_94
end Pool039Finite
```

### `CertificateChunk95.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_95 : List ℕ := [4,32,4,32,32,32,4,52,20,16,68,20,4,36,4,40,40,40,40,40,40,16,52,20,16,84,20,16,125,20,4,32,4,40,40,40,24,52,52,24,61,52,24,61,61,32,32,32,32,32,32,16,112,109,16,61,93,16,61,61,4,44,12,61,44,44,4,100,117,28,76,28,12,76,12,8,68,12,61,100,36,8,100,117,68,68,36,12,121,12,4,36,4,61,36,36,4,100,117,20,68,20,4,68,4]
theorem certificate_chunk_95 :
 checkRows ((matchings 4 [2,3,4,5,6,8,9,10]).map (fun E => [(0,11),(1,7)] ++ E)) codes_95 = true := by decide +kernel
#print axioms certificate_chunk_95
end Pool039Finite
```

### `CertificateChunk96.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_96 : List ℕ := [0,36,4,16,36,36,0,96,117,20,68,20,4,68,4,8,104,125,16,104,125,8,104,117,20,80,20,20,125,20,0,36,4,24,104,125,8,104,117,88,88,48,125,125,61,8,36,36,32,36,36,8,104,109,20,88,56,20,93,61,0,96,109,16,96,109,0,96,109,80,80,48,93,93,61,12,68,12,61,61,36,12,61,93,68,68,36,12,109,12,4,68,4,61,61,36,4,61,93,68,68,36,4,109,4]
theorem certificate_chunk_96 :
 checkRows ((matchings 4 [2,3,4,5,6,7,9,10]).map (fun E => [(0,11),(1,8)] ++ E)) codes_96 = true := by decide +kernel
#print axioms certificate_chunk_96
end Pool039Finite
```

### `CertificateChunk97.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_97 : List ℕ := [4,64,4,80,80,32,4,80,48,64,64,32,4,117,4,72,72,40,80,80,40,72,80,48,72,72,40,16,117,16,4,64,4,88,88,40,72,88,48,72,72,40,24,117,24,72,72,32,96,96,32,72,88,56,72,72,40,16,117,24,4,72,40,80,96,40,4,96,121,72,72,40,24,117,24,64,64,32,80,80,32,64,80,48,64,64,32,16,117,16,4,109,4,61,61,61,4,61,61,93,93,61,4,109,4]
theorem certificate_chunk_97 :
 checkRows ((matchings 4 [2,3,4,5,6,7,8,10]).map (fun E => [(0,11),(1,9)] ++ E)) codes_97 = true := by decide +kernel
#print axioms certificate_chunk_97
end Pool039Finite
```

### `CertificateChunk98.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def codes_98 : List ℕ := [0,32,0,16,32,16,0,48,16,16,64,16,0,32,0,8,40,8,16,40,16,8,48,16,16,72,16,8,40,8,0,32,0,24,40,24,8,48,24,24,72,24,8,40,8,8,32,8,32,32,32,8,56,24,16,72,24,8,40,8,0,40,8,16,40,40,0,96,121,24,72,24,8,72,8,8,64,8,80,80,32,8,80,48,64,64,32,8,121,8,0,32,0,16,32,16,0,48,16,16,64,16,0,32,0]
theorem certificate_chunk_98 :
 checkRows ((matchings 4 [2,3,4,5,6,7,8,9]).map (fun E => [(0,11),(1,10)] ++ E)) codes_98 = true := by decide +kernel
#print axioms certificate_chunk_98
end Pool039Finite
```

### `CertificateSmall0_0.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_0_0 : List ℕ := [0]
theorem certificate_small_0_0 :
 checkRows ((matchings 0 []).map (fun E => [] ++ E)) smallcodes_0_0 = true := by decide +kernel
#print axioms certificate_small_0_0
end Pool039Finite
```

### `CertificateSmall1_0.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_1_0 : List ℕ := [0]
theorem certificate_small_1_0 :
 checkRows ((matchings 1 [0,1]).map (fun E => [] ++ E)) smallcodes_1_0 = true := by decide +kernel
#print axioms certificate_small_1_0
end Pool039Finite
```

### `CertificateSmall2_0.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_2_0 : List ℕ := [0,2,0]
theorem certificate_small_2_0 :
 checkRows ((matchings 2 [0,1,2,3]).map (fun E => [] ++ E)) smallcodes_2_0 = true := by decide +kernel
#print axioms certificate_small_2_0
end Pool039Finite
```

### `CertificateSmall3_0.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_3_0 : List ℕ := [0,4,0,2,4,2,0,6,2,2,8,2,0,4,0]
theorem certificate_small_3_0 :
 checkRows ((matchings 3 [0,1,2,3,4,5]).map (fun E => [] ++ E)) smallcodes_3_0 = true := by decide +kernel
#print axioms certificate_small_3_0
end Pool039Finite
```

### `CertificateSmall4_0.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_4_0 : List ℕ := [0,8,0,4,8,4,0,12,4,4,16,4,0,8,0]
theorem certificate_small_4_0 :
 checkRows ((matchings 3 [2,3,4,5,6,7]).map (fun E => [(0,1)] ++ E)) smallcodes_4_0 = true := by decide +kernel
#print axioms certificate_small_4_0
end Pool039Finite
```

### `CertificateSmall4_1.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_4_1 : List ℕ := [2,10,2,4,10,4,2,12,4,4,18,4,2,10,2]
theorem certificate_small_4_1 :
 checkRows ((matchings 3 [1,3,4,5,6,7]).map (fun E => [(0,2)] ++ E)) smallcodes_4_1 = true := by decide +kernel
#print axioms certificate_small_4_1
end Pool039Finite
```

### `CertificateSmall4_2.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_4_2 : List ℕ := [0,8,0,6,10,6,2,12,6,6,18,6,2,10,2]
theorem certificate_small_4_2 :
 checkRows ((matchings 3 [1,2,4,5,6,7]).map (fun E => [(0,3)] ++ E)) smallcodes_4_2 = true := by decide +kernel
#print axioms certificate_small_4_2
end Pool039Finite
```

### `CertificateSmall4_3.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_4_3 : List ℕ := [2,8,2,8,8,8,2,14,6,4,18,6,2,10,2]
theorem certificate_small_4_3 :
 checkRows ((matchings 3 [1,2,3,5,6,7]).map (fun E => [(0,4)] ++ E)) smallcodes_4_3 = true := by decide +kernel
#print axioms certificate_small_4_3
end Pool039Finite
```

### `CertificateSmall4_4.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_4_4 : List ℕ := [0,10,2,4,10,10,0,24,31,6,18,6,2,18,2]
theorem certificate_small_4_4 :
 checkRows ((matchings 3 [1,2,3,4,6,7]).map (fun E => [(0,5)] ++ E)) smallcodes_4_4 = true := by decide +kernel
#print axioms certificate_small_4_4
end Pool039Finite
```

### `CertificateSmall4_5.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_4_5 : List ℕ := [2,16,2,20,20,8,2,20,12,16,16,8,2,31,2]
theorem certificate_small_4_5 :
 checkRows ((matchings 3 [1,2,3,4,5,7]).map (fun E => [(0,6)] ++ E)) smallcodes_4_5 = true := by decide +kernel
#print axioms certificate_small_4_5
end Pool039Finite
```

### `CertificateSmall4_6.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_4_6 : List ℕ := [0,8,0,4,8,4,0,12,4,4,16,4,0,8,0]
theorem certificate_small_4_6 :
 checkRows ((matchings 3 [1,2,3,4,5,6]).map (fun E => [(0,7)] ++ E)) smallcodes_4_6 = true := by decide +kernel
#print axioms certificate_small_4_6
end Pool039Finite
```

### `CertificateSmall5_0.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_5_0 : List ℕ := [0,16,0,8,16,8,0,24,8,8,32,8,0,16,0,4,20,4,8,20,8,4,24,8,8,36,8,4,20,4,0,16,0,12,20,12,4,24,12,12,36,12,4,20,4,4,16,4,16,16,16,4,28,12,8,36,12,4,20,4,0,20,4,8,20,20,0,48,61,12,36,12,4,36,4,4,32,4,40,40,16,4,40,24,32,32,16,4,61,4,0,16,0,8,16,8,0,24,8,8,32,8,0,16,0]
theorem certificate_small_5_0 :
 checkRows ((matchings 4 [2,3,4,5,6,7,8,9]).map (fun E => [(0,1)] ++ E)) smallcodes_5_0 = true := by decide +kernel
#print axioms certificate_small_5_0
end Pool039Finite
```

### `CertificateSmall5_1.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_5_1 : List ℕ := [2,18,2,10,18,10,2,26,10,10,34,10,2,18,2,4,20,4,10,20,10,4,26,10,10,36,10,4,20,4,2,18,2,12,20,12,4,26,12,12,36,12,4,20,4,4,18,4,18,18,18,4,28,12,10,36,12,4,20,4,2,20,4,10,20,20,2,50,61,12,36,12,4,36,4,4,34,4,42,42,18,4,42,26,34,34,18,4,61,4,2,18,2,10,18,10,2,26,10,10,34,10,2,18,2]
theorem certificate_small_5_1 :
 checkRows ((matchings 4 [1,3,4,5,6,7,8,9]).map (fun E => [(0,2)] ++ E)) smallcodes_5_1 = true := by decide +kernel
#print axioms certificate_small_5_1
end Pool039Finite
```

### `CertificateSmall5_2.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_5_2 : List ℕ := [0,16,0,8,16,8,0,24,8,8,32,8,0,16,0,6,22,6,10,22,10,6,26,10,10,38,10,6,22,6,2,18,2,12,22,12,6,26,12,12,38,12,6,22,6,6,18,6,18,18,18,6,28,12,10,38,12,6,22,6,2,22,6,10,22,22,2,50,61,12,38,12,6,38,6,6,34,6,42,42,18,6,42,26,34,34,18,6,61,6,2,18,2,10,18,10,2,26,10,10,34,10,2,18,2]
theorem certificate_small_5_2 :
 checkRows ((matchings 4 [1,2,4,5,6,7,8,9]).map (fun E => [(0,3)] ++ E)) smallcodes_5_2 = true := by decide +kernel
#print axioms certificate_small_5_2
end Pool039Finite
```

### `CertificateSmall5_3.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_5_3 : List ℕ := [2,18,2,8,18,8,2,24,8,8,34,8,2,18,2,8,24,8,8,24,8,8,24,8,8,40,8,8,63,8,2,18,2,14,22,14,6,26,14,14,38,14,6,22,6,4,18,4,18,18,18,6,28,14,10,38,14,6,22,6,2,20,4,10,22,22,2,50,61,14,38,14,6,38,6,4,34,4,42,42,18,6,42,26,34,34,18,6,61,6,2,18,2,10,18,10,2,26,10,10,34,10,2,18,2]
theorem certificate_small_5_3 :
 checkRows ((matchings 4 [1,2,3,5,6,7,8,9]).map (fun E => [(0,4)] ++ E)) smallcodes_5_3 = true := by decide +kernel
#print axioms certificate_small_5_3
end Pool039Finite
```

### `CertificateSmall5_4.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_5_4 : List ℕ := [0,16,0,10,18,10,2,24,10,10,34,10,2,18,2,4,20,4,10,24,10,10,24,10,10,42,10,10,63,10,0,16,0,24,24,24,31,24,24,31,31,24,31,31,31,6,18,6,18,18,18,6,30,14,10,38,14,6,22,6,2,20,6,18,20,20,2,50,61,12,38,14,6,38,6,6,34,6,50,50,18,6,42,26,34,34,18,6,61,6,2,18,2,18,18,18,2,26,10,10,34,10,2,18,2]
theorem certificate_small_5_4 :
 checkRows ((matchings 4 [1,2,3,4,6,7,8,9]).map (fun E => [(0,5)] ++ E)) smallcodes_5_4 = true := by decide +kernel
#print axioms certificate_small_5_4
end Pool039Finite
```

### `CertificateSmall5_5.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_5_5 : List ℕ := [2,16,2,16,16,16,2,26,10,8,34,10,2,18,2,20,20,20,20,20,20,8,26,10,8,42,10,8,63,10,2,16,2,20,20,20,12,26,26,12,31,26,12,31,31,16,16,16,16,16,16,8,56,55,8,31,47,8,31,31,2,22,6,31,22,22,2,50,59,14,38,14,6,38,6,4,34,6,31,50,18,4,50,59,34,34,18,6,61,6,2,18,2,31,18,18,2,50,59,10,34,10,2,34,2]
theorem certificate_small_5_5 :
 checkRows ((matchings 4 [1,2,3,4,5,7,8,9]).map (fun E => [(0,6)] ++ E)) smallcodes_5_5 = true := by decide +kernel
#print axioms certificate_small_5_5
end Pool039Finite
```

### `CertificateSmall5_6.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_5_6 : List ℕ := [0,18,2,8,18,18,0,48,59,10,34,10,2,34,2,4,52,63,8,52,63,4,52,59,10,40,10,10,63,10,0,18,2,12,52,63,4,52,59,44,44,24,63,63,31,4,18,18,16,18,18,4,52,55,10,44,28,10,47,31,0,48,55,8,48,55,0,48,55,40,40,24,47,47,31,6,34,6,31,31,18,6,31,47,34,34,18,6,55,6,2,34,2,31,31,18,2,31,47,34,34,18,2,55,2]
theorem certificate_small_5_6 :
 checkRows ((matchings 4 [1,2,3,4,5,6,8,9]).map (fun E => [(0,7)] ++ E)) smallcodes_5_6 = true := by decide +kernel
#print axioms certificate_small_5_6
end Pool039Finite
```

### `CertificateSmall5_7.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_5_7 : List ℕ := [2,32,2,40,40,16,2,40,24,32,32,16,2,59,2,36,36,20,40,40,20,36,40,24,36,36,20,8,59,8,2,32,2,44,44,20,36,44,24,36,36,20,12,59,12,36,36,16,48,48,16,36,44,28,36,36,20,8,59,12,2,36,20,40,48,20,2,48,61,36,36,20,12,59,12,32,32,16,40,40,16,32,40,24,32,32,16,8,59,8,2,55,2,31,31,31,2,31,31,47,47,31,2,55,2]
theorem certificate_small_5_7 :
 checkRows ((matchings 4 [1,2,3,4,5,6,7,9]).map (fun E => [(0,8)] ++ E)) smallcodes_5_7 = true := by decide +kernel
#print axioms certificate_small_5_7
end Pool039Finite
```

### `CertificateSmall5_8.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Pool039Finite
def smallcodes_5_8 : List ℕ := [0,16,0,8,16,8,0,24,8,8,32,8,0,16,0,4,20,4,8,20,8,4,24,8,8,36,8,4,20,4,0,16,0,12,20,12,4,24,12,12,36,12,4,20,4,4,16,4,16,16,16,4,28,12,8,36,12,4,20,4,0,20,4,8,20,20,0,48,61,12,36,12,4,36,4,4,32,4,40,40,16,4,40,24,32,32,16,4,61,4,0,16,0,8,16,8,0,24,8,8,32,8,0,16,0]
theorem certificate_small_5_8 :
 checkRows ((matchings 4 [1,2,3,4,5,6,7,8]).map (fun E => [(0,9)] ++ E)) smallcodes_5_8 = true := by decide +kernel
#print axioms certificate_small_5_8
end Pool039Finite
```

### `CertificateCoverageDefs.lean`

```lean
import FiniteDefs
set_option maxHeartbeats 0
namespace Pool039Finite

def Covered (rows : List (List Arc)) : Prop :=
  ∀ E ∈ rows, ∃ code, checkRow E code = true

theorem covered_of_checkRows {rows codes} (h : checkRows rows codes = true) : Covered rows := by
  induction rows generalizing codes with
  | nil => simp [Covered]
  | cons E rows ih =>
    cases codes with
    | nil => simp [checkRows] at h
    | cons c codes =>
      have hh := Bool.and_eq_true_iff.mp h
      intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨c,hh.1⟩
      · exact ih hh.2 F hF

theorem covered_flatMap {α : Type} (xs : List α) (f : α → List (List Arc))
    (h : ∀ x ∈ xs, Covered (f x)) : Covered (xs.flatMap f) := by
  intro E hE
  obtain ⟨x,hx,hEx⟩ := List.mem_flatMap.mp hE
  exact h x hx E hEx

end Pool039Finite
```

### `CoverageSmall.lean`

```lean
import CertificateCoverageDefs
import CertificateSmall0_0
import CertificateSmall1_0
import CertificateSmall2_0
import CertificateSmall3_0
import CertificateSmall4_0
import CertificateSmall4_1
import CertificateSmall4_2
import CertificateSmall4_3
import CertificateSmall4_4
import CertificateSmall4_5
import CertificateSmall4_6
import CertificateSmall5_0
import CertificateSmall5_1
import CertificateSmall5_2
import CertificateSmall5_3
import CertificateSmall5_4
import CertificateSmall5_5
import CertificateSmall5_6
import CertificateSmall5_7
import CertificateSmall5_8

namespace Pool039Finite
set_option maxHeartbeats 0

theorem covered_0 : Covered (matchings 0 (List.range 0)) := by
  exact covered_of_checkRows certificate_small_0_0

theorem covered_1 : Covered (matchings 1 (List.range 2)) := by
  exact covered_of_checkRows certificate_small_1_0

theorem covered_2 : Covered (matchings 2 (List.range 4)) := by
  exact covered_of_checkRows certificate_small_2_0

theorem covered_3 : Covered (matchings 3 (List.range 6)) := by
  exact covered_of_checkRows certificate_small_3_0

theorem covered_4 : Covered (matchings 4 (List.range 8)) := by
  change Covered ([1,2,3,4,5,6,7].flatMap (fun b => (matchings 3 ([1,2,3,4,5,6,7].erase b)).map (fun E => (0,b)::E)))
  apply covered_flatMap
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covered_of_checkRows certificate_small_4_0
  · exact covered_of_checkRows certificate_small_4_1
  · exact covered_of_checkRows certificate_small_4_2
  · exact covered_of_checkRows certificate_small_4_3
  · exact covered_of_checkRows certificate_small_4_4
  · exact covered_of_checkRows certificate_small_4_5
  · exact covered_of_checkRows certificate_small_4_6

theorem covered_5 : Covered (matchings 5 (List.range 10)) := by
  change Covered ([1,2,3,4,5,6,7,8,9].flatMap (fun b => (matchings 4 ([1,2,3,4,5,6,7,8,9].erase b)).map (fun E => (0,b)::E)))
  apply covered_flatMap
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covered_of_checkRows certificate_small_5_0
  · exact covered_of_checkRows certificate_small_5_1
  · exact covered_of_checkRows certificate_small_5_2
  · exact covered_of_checkRows certificate_small_5_3
  · exact covered_of_checkRows certificate_small_5_4
  · exact covered_of_checkRows certificate_small_5_5
  · exact covered_of_checkRows certificate_small_5_6
  · exact covered_of_checkRows certificate_small_5_7
  · exact covered_of_checkRows certificate_small_5_8

end Pool039Finite
```

### `CoverageBranches.lean`

```lean
import CertificateCoverageDefs

namespace Pool039Finite
set_option maxHeartbeats 0

theorem covered_6_of_branches
    (h0 : Covered ((matchings 4 [4,5,6,7,8,9,10,11]).map (fun E => [(0,1),(2,3)] ++ E)))
    (h1 : Covered ((matchings 4 [3,5,6,7,8,9,10,11]).map (fun E => [(0,1),(2,4)] ++ E)))
    (h2 : Covered ((matchings 4 [3,4,6,7,8,9,10,11]).map (fun E => [(0,1),(2,5)] ++ E)))
    (h3 : Covered ((matchings 4 [3,4,5,7,8,9,10,11]).map (fun E => [(0,1),(2,6)] ++ E)))
    (h4 : Covered ((matchings 4 [3,4,5,6,8,9,10,11]).map (fun E => [(0,1),(2,7)] ++ E)))
    (h5 : Covered ((matchings 4 [3,4,5,6,7,9,10,11]).map (fun E => [(0,1),(2,8)] ++ E)))
    (h6 : Covered ((matchings 4 [3,4,5,6,7,8,10,11]).map (fun E => [(0,1),(2,9)] ++ E)))
    (h7 : Covered ((matchings 4 [3,4,5,6,7,8,9,11]).map (fun E => [(0,1),(2,10)] ++ E)))
    (h8 : Covered ((matchings 4 [3,4,5,6,7,8,9,10]).map (fun E => [(0,1),(2,11)] ++ E)))
    (h9 : Covered ((matchings 4 [4,5,6,7,8,9,10,11]).map (fun E => [(0,2),(1,3)] ++ E)))
    (h10 : Covered ((matchings 4 [3,5,6,7,8,9,10,11]).map (fun E => [(0,2),(1,4)] ++ E)))
    (h11 : Covered ((matchings 4 [3,4,6,7,8,9,10,11]).map (fun E => [(0,2),(1,5)] ++ E)))
    (h12 : Covered ((matchings 4 [3,4,5,7,8,9,10,11]).map (fun E => [(0,2),(1,6)] ++ E)))
    (h13 : Covered ((matchings 4 [3,4,5,6,8,9,10,11]).map (fun E => [(0,2),(1,7)] ++ E)))
    (h14 : Covered ((matchings 4 [3,4,5,6,7,9,10,11]).map (fun E => [(0,2),(1,8)] ++ E)))
    (h15 : Covered ((matchings 4 [3,4,5,6,7,8,10,11]).map (fun E => [(0,2),(1,9)] ++ E)))
    (h16 : Covered ((matchings 4 [3,4,5,6,7,8,9,11]).map (fun E => [(0,2),(1,10)] ++ E)))
    (h17 : Covered ((matchings 4 [3,4,5,6,7,8,9,10]).map (fun E => [(0,2),(1,11)] ++ E)))
    (h18 : Covered ((matchings 4 [4,5,6,7,8,9,10,11]).map (fun E => [(0,3),(1,2)] ++ E)))
    (h19 : Covered ((matchings 4 [2,5,6,7,8,9,10,11]).map (fun E => [(0,3),(1,4)] ++ E)))
    (h20 : Covered ((matchings 4 [2,4,6,7,8,9,10,11]).map (fun E => [(0,3),(1,5)] ++ E)))
    (h21 : Covered ((matchings 4 [2,4,5,7,8,9,10,11]).map (fun E => [(0,3),(1,6)] ++ E)))
    (h22 : Covered ((matchings 4 [2,4,5,6,8,9,10,11]).map (fun E => [(0,3),(1,7)] ++ E)))
    (h23 : Covered ((matchings 4 [2,4,5,6,7,9,10,11]).map (fun E => [(0,3),(1,8)] ++ E)))
    (h24 : Covered ((matchings 4 [2,4,5,6,7,8,10,11]).map (fun E => [(0,3),(1,9)] ++ E)))
    (h25 : Covered ((matchings 4 [2,4,5,6,7,8,9,11]).map (fun E => [(0,3),(1,10)] ++ E)))
    (h26 : Covered ((matchings 4 [2,4,5,6,7,8,9,10]).map (fun E => [(0,3),(1,11)] ++ E)))
    (h27 : Covered ((matchings 4 [3,5,6,7,8,9,10,11]).map (fun E => [(0,4),(1,2)] ++ E)))
    (h28 : Covered ((matchings 4 [2,5,6,7,8,9,10,11]).map (fun E => [(0,4),(1,3)] ++ E)))
    (h29 : Covered ((matchings 4 [2,3,6,7,8,9,10,11]).map (fun E => [(0,4),(1,5)] ++ E)))
    (h30 : Covered ((matchings 4 [2,3,5,7,8,9,10,11]).map (fun E => [(0,4),(1,6)] ++ E)))
    (h31 : Covered ((matchings 4 [2,3,5,6,8,9,10,11]).map (fun E => [(0,4),(1,7)] ++ E)))
    (h32 : Covered ((matchings 4 [2,3,5,6,7,9,10,11]).map (fun E => [(0,4),(1,8)] ++ E)))
    (h33 : Covered ((matchings 4 [2,3,5,6,7,8,10,11]).map (fun E => [(0,4),(1,9)] ++ E)))
    (h34 : Covered ((matchings 4 [2,3,5,6,7,8,9,11]).map (fun E => [(0,4),(1,10)] ++ E)))
    (h35 : Covered ((matchings 4 [2,3,5,6,7,8,9,10]).map (fun E => [(0,4),(1,11)] ++ E)))
    (h36 : Covered ((matchings 4 [3,4,6,7,8,9,10,11]).map (fun E => [(0,5),(1,2)] ++ E)))
    (h37 : Covered ((matchings 4 [2,4,6,7,8,9,10,11]).map (fun E => [(0,5),(1,3)] ++ E)))
    (h38 : Covered ((matchings 4 [2,3,6,7,8,9,10,11]).map (fun E => [(0,5),(1,4)] ++ E)))
    (h39 : Covered ((matchings 4 [2,3,4,7,8,9,10,11]).map (fun E => [(0,5),(1,6)] ++ E)))
    (h40 : Covered ((matchings 4 [2,3,4,6,8,9,10,11]).map (fun E => [(0,5),(1,7)] ++ E)))
    (h41 : Covered ((matchings 4 [2,3,4,6,7,9,10,11]).map (fun E => [(0,5),(1,8)] ++ E)))
    (h42 : Covered ((matchings 4 [2,3,4,6,7,8,10,11]).map (fun E => [(0,5),(1,9)] ++ E)))
    (h43 : Covered ((matchings 4 [2,3,4,6,7,8,9,11]).map (fun E => [(0,5),(1,10)] ++ E)))
    (h44 : Covered ((matchings 4 [2,3,4,6,7,8,9,10]).map (fun E => [(0,5),(1,11)] ++ E)))
    (h45 : Covered ((matchings 4 [3,4,5,7,8,9,10,11]).map (fun E => [(0,6),(1,2)] ++ E)))
    (h46 : Covered ((matchings 4 [2,4,5,7,8,9,10,11]).map (fun E => [(0,6),(1,3)] ++ E)))
    (h47 : Covered ((matchings 4 [2,3,5,7,8,9,10,11]).map (fun E => [(0,6),(1,4)] ++ E)))
    (h48 : Covered ((matchings 4 [2,3,4,7,8,9,10,11]).map (fun E => [(0,6),(1,5)] ++ E)))
    (h49 : Covered ((matchings 4 [2,3,4,5,8,9,10,11]).map (fun E => [(0,6),(1,7)] ++ E)))
    (h50 : Covered ((matchings 4 [2,3,4,5,7,9,10,11]).map (fun E => [(0,6),(1,8)] ++ E)))
    (h51 : Covered ((matchings 4 [2,3,4,5,7,8,10,11]).map (fun E => [(0,6),(1,9)] ++ E)))
    (h52 : Covered ((matchings 4 [2,3,4,5,7,8,9,11]).map (fun E => [(0,6),(1,10)] ++ E)))
    (h53 : Covered ((matchings 4 [2,3,4,5,7,8,9,10]).map (fun E => [(0,6),(1,11)] ++ E)))
    (h54 : Covered ((matchings 4 [3,4,5,6,8,9,10,11]).map (fun E => [(0,7),(1,2)] ++ E)))
    (h55 : Covered ((matchings 4 [2,4,5,6,8,9,10,11]).map (fun E => [(0,7),(1,3)] ++ E)))
    (h56 : Covered ((matchings 4 [2,3,5,6,8,9,10,11]).map (fun E => [(0,7),(1,4)] ++ E)))
    (h57 : Covered ((matchings 4 [2,3,4,6,8,9,10,11]).map (fun E => [(0,7),(1,5)] ++ E)))
    (h58 : Covered ((matchings 4 [2,3,4,5,8,9,10,11]).map (fun E => [(0,7),(1,6)] ++ E)))
    (h59 : Covered ((matchings 4 [2,3,4,5,6,9,10,11]).map (fun E => [(0,7),(1,8)] ++ E)))
    (h60 : Covered ((matchings 4 [2,3,4,5,6,8,10,11]).map (fun E => [(0,7),(1,9)] ++ E)))
    (h61 : Covered ((matchings 4 [2,3,4,5,6,8,9,11]).map (fun E => [(0,7),(1,10)] ++ E)))
    (h62 : Covered ((matchings 4 [2,3,4,5,6,8,9,10]).map (fun E => [(0,7),(1,11)] ++ E)))
    (h63 : Covered ((matchings 4 [3,4,5,6,7,9,10,11]).map (fun E => [(0,8),(1,2)] ++ E)))
    (h64 : Covered ((matchings 4 [2,4,5,6,7,9,10,11]).map (fun E => [(0,8),(1,3)] ++ E)))
    (h65 : Covered ((matchings 4 [2,3,5,6,7,9,10,11]).map (fun E => [(0,8),(1,4)] ++ E)))
    (h66 : Covered ((matchings 4 [2,3,4,6,7,9,10,11]).map (fun E => [(0,8),(1,5)] ++ E)))
    (h67 : Covered ((matchings 4 [2,3,4,5,7,9,10,11]).map (fun E => [(0,8),(1,6)] ++ E)))
    (h68 : Covered ((matchings 4 [2,3,4,5,6,9,10,11]).map (fun E => [(0,8),(1,7)] ++ E)))
    (h69 : Covered ((matchings 4 [2,3,4,5,6,7,10,11]).map (fun E => [(0,8),(1,9)] ++ E)))
    (h70 : Covered ((matchings 4 [2,3,4,5,6,7,9,11]).map (fun E => [(0,8),(1,10)] ++ E)))
    (h71 : Covered ((matchings 4 [2,3,4,5,6,7,9,10]).map (fun E => [(0,8),(1,11)] ++ E)))
    (h72 : Covered ((matchings 4 [3,4,5,6,7,8,10,11]).map (fun E => [(0,9),(1,2)] ++ E)))
    (h73 : Covered ((matchings 4 [2,4,5,6,7,8,10,11]).map (fun E => [(0,9),(1,3)] ++ E)))
    (h74 : Covered ((matchings 4 [2,3,5,6,7,8,10,11]).map (fun E => [(0,9),(1,4)] ++ E)))
    (h75 : Covered ((matchings 4 [2,3,4,6,7,8,10,11]).map (fun E => [(0,9),(1,5)] ++ E)))
    (h76 : Covered ((matchings 4 [2,3,4,5,7,8,10,11]).map (fun E => [(0,9),(1,6)] ++ E)))
    (h77 : Covered ((matchings 4 [2,3,4,5,6,8,10,11]).map (fun E => [(0,9),(1,7)] ++ E)))
    (h78 : Covered ((matchings 4 [2,3,4,5,6,7,10,11]).map (fun E => [(0,9),(1,8)] ++ E)))
    (h79 : Covered ((matchings 4 [2,3,4,5,6,7,8,11]).map (fun E => [(0,9),(1,10)] ++ E)))
    (h80 : Covered ((matchings 4 [2,3,4,5,6,7,8,10]).map (fun E => [(0,9),(1,11)] ++ E)))
    (h81 : Covered ((matchings 4 [3,4,5,6,7,8,9,11]).map (fun E => [(0,10),(1,2)] ++ E)))
    (h82 : Covered ((matchings 4 [2,4,5,6,7,8,9,11]).map (fun E => [(0,10),(1,3)] ++ E)))
    (h83 : Covered ((matchings 4 [2,3,5,6,7,8,9,11]).map (fun E => [(0,10),(1,4)] ++ E)))
    (h84 : Covered ((matchings 4 [2,3,4,6,7,8,9,11]).map (fun E => [(0,10),(1,5)] ++ E)))
    (h85 : Covered ((matchings 4 [2,3,4,5,7,8,9,11]).map (fun E => [(0,10),(1,6)] ++ E)))
    (h86 : Covered ((matchings 4 [2,3,4,5,6,8,9,11]).map (fun E => [(0,10),(1,7)] ++ E)))
    (h87 : Covered ((matchings 4 [2,3,4,5,6,7,9,11]).map (fun E => [(0,10),(1,8)] ++ E)))
    (h88 : Covered ((matchings 4 [2,3,4,5,6,7,8,11]).map (fun E => [(0,10),(1,9)] ++ E)))
    (h89 : Covered ((matchings 4 [2,3,4,5,6,7,8,9]).map (fun E => [(0,10),(1,11)] ++ E)))
    (h90 : Covered ((matchings 4 [3,4,5,6,7,8,9,10]).map (fun E => [(0,11),(1,2)] ++ E)))
    (h91 : Covered ((matchings 4 [2,4,5,6,7,8,9,10]).map (fun E => [(0,11),(1,3)] ++ E)))
    (h92 : Covered ((matchings 4 [2,3,5,6,7,8,9,10]).map (fun E => [(0,11),(1,4)] ++ E)))
    (h93 : Covered ((matchings 4 [2,3,4,6,7,8,9,10]).map (fun E => [(0,11),(1,5)] ++ E)))
    (h94 : Covered ((matchings 4 [2,3,4,5,7,8,9,10]).map (fun E => [(0,11),(1,6)] ++ E)))
    (h95 : Covered ((matchings 4 [2,3,4,5,6,8,9,10]).map (fun E => [(0,11),(1,7)] ++ E)))
    (h96 : Covered ((matchings 4 [2,3,4,5,6,7,9,10]).map (fun E => [(0,11),(1,8)] ++ E)))
    (h97 : Covered ((matchings 4 [2,3,4,5,6,7,8,10]).map (fun E => [(0,11),(1,9)] ++ E)))
    (h98 : Covered ((matchings 4 [2,3,4,5,6,7,8,9]).map (fun E => [(0,11),(1,10)] ++ E)))
    : Covered (matchings 6 (List.range 12)) := by
  change Covered ([1,2,3,4,5,6,7,8,9,10,11].flatMap (fun b => (matchings 5 ([1,2,3,4,5,6,7,8,9,10,11].erase b)).map (fun E => (0,b)::E)))
  apply covered_flatMap
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Covered (([3,4,5,6,7,8,9,10,11].flatMap (fun c => (matchings 4 ([3,4,5,6,7,8,9,10,11].erase c)).map (fun E => (2,c)::E))).map (fun E => (0,1)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h0
    · rw [List.map_map]; exact h1
    · rw [List.map_map]; exact h2
    · rw [List.map_map]; exact h3
    · rw [List.map_map]; exact h4
    · rw [List.map_map]; exact h5
    · rw [List.map_map]; exact h6
    · rw [List.map_map]; exact h7
    · rw [List.map_map]; exact h8
  · change Covered (([3,4,5,6,7,8,9,10,11].flatMap (fun c => (matchings 4 ([3,4,5,6,7,8,9,10,11].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,2)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h9
    · rw [List.map_map]; exact h10
    · rw [List.map_map]; exact h11
    · rw [List.map_map]; exact h12
    · rw [List.map_map]; exact h13
    · rw [List.map_map]; exact h14
    · rw [List.map_map]; exact h15
    · rw [List.map_map]; exact h16
    · rw [List.map_map]; exact h17
  · change Covered (([2,4,5,6,7,8,9,10,11].flatMap (fun c => (matchings 4 ([2,4,5,6,7,8,9,10,11].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,3)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h18
    · rw [List.map_map]; exact h19
    · rw [List.map_map]; exact h20
    · rw [List.map_map]; exact h21
    · rw [List.map_map]; exact h22
    · rw [List.map_map]; exact h23
    · rw [List.map_map]; exact h24
    · rw [List.map_map]; exact h25
    · rw [List.map_map]; exact h26
  · change Covered (([2,3,5,6,7,8,9,10,11].flatMap (fun c => (matchings 4 ([2,3,5,6,7,8,9,10,11].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,4)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h27
    · rw [List.map_map]; exact h28
    · rw [List.map_map]; exact h29
    · rw [List.map_map]; exact h30
    · rw [List.map_map]; exact h31
    · rw [List.map_map]; exact h32
    · rw [List.map_map]; exact h33
    · rw [List.map_map]; exact h34
    · rw [List.map_map]; exact h35
  · change Covered (([2,3,4,6,7,8,9,10,11].flatMap (fun c => (matchings 4 ([2,3,4,6,7,8,9,10,11].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,5)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h36
    · rw [List.map_map]; exact h37
    · rw [List.map_map]; exact h38
    · rw [List.map_map]; exact h39
    · rw [List.map_map]; exact h40
    · rw [List.map_map]; exact h41
    · rw [List.map_map]; exact h42
    · rw [List.map_map]; exact h43
    · rw [List.map_map]; exact h44
  · change Covered (([2,3,4,5,7,8,9,10,11].flatMap (fun c => (matchings 4 ([2,3,4,5,7,8,9,10,11].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,6)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h45
    · rw [List.map_map]; exact h46
    · rw [List.map_map]; exact h47
    · rw [List.map_map]; exact h48
    · rw [List.map_map]; exact h49
    · rw [List.map_map]; exact h50
    · rw [List.map_map]; exact h51
    · rw [List.map_map]; exact h52
    · rw [List.map_map]; exact h53
  · change Covered (([2,3,4,5,6,8,9,10,11].flatMap (fun c => (matchings 4 ([2,3,4,5,6,8,9,10,11].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,7)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h54
    · rw [List.map_map]; exact h55
    · rw [List.map_map]; exact h56
    · rw [List.map_map]; exact h57
    · rw [List.map_map]; exact h58
    · rw [List.map_map]; exact h59
    · rw [List.map_map]; exact h60
    · rw [List.map_map]; exact h61
    · rw [List.map_map]; exact h62
  · change Covered (([2,3,4,5,6,7,9,10,11].flatMap (fun c => (matchings 4 ([2,3,4,5,6,7,9,10,11].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,8)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h63
    · rw [List.map_map]; exact h64
    · rw [List.map_map]; exact h65
    · rw [List.map_map]; exact h66
    · rw [List.map_map]; exact h67
    · rw [List.map_map]; exact h68
    · rw [List.map_map]; exact h69
    · rw [List.map_map]; exact h70
    · rw [List.map_map]; exact h71
  · change Covered (([2,3,4,5,6,7,8,10,11].flatMap (fun c => (matchings 4 ([2,3,4,5,6,7,8,10,11].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,9)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h72
    · rw [List.map_map]; exact h73
    · rw [List.map_map]; exact h74
    · rw [List.map_map]; exact h75
    · rw [List.map_map]; exact h76
    · rw [List.map_map]; exact h77
    · rw [List.map_map]; exact h78
    · rw [List.map_map]; exact h79
    · rw [List.map_map]; exact h80
  · change Covered (([2,3,4,5,6,7,8,9,11].flatMap (fun c => (matchings 4 ([2,3,4,5,6,7,8,9,11].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,10)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h81
    · rw [List.map_map]; exact h82
    · rw [List.map_map]; exact h83
    · rw [List.map_map]; exact h84
    · rw [List.map_map]; exact h85
    · rw [List.map_map]; exact h86
    · rw [List.map_map]; exact h87
    · rw [List.map_map]; exact h88
    · rw [List.map_map]; exact h89
  · change Covered (([2,3,4,5,6,7,8,9,10].flatMap (fun c => (matchings 4 ([2,3,4,5,6,7,8,9,10].erase c)).map (fun E => (1,c)::E))).map (fun E => (0,11)::E))
    rw [List.map_flatMap]
    apply covered_flatMap
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.map_map]; exact h90
    · rw [List.map_map]; exact h91
    · rw [List.map_map]; exact h92
    · rw [List.map_map]; exact h93
    · rw [List.map_map]; exact h94
    · rw [List.map_map]; exact h95
    · rw [List.map_map]; exact h96
    · rw [List.map_map]; exact h97
    · rw [List.map_map]; exact h98

#print axioms covered_6_of_branches
end Pool039Finite
```

### `CoverageSix.lean`

```lean
import CoverageBranches
import CertificateChunk0
import CertificateChunk1
import CertificateChunk2
import CertificateChunk3
import CertificateChunk4
import CertificateChunk5
import CertificateChunk6
import CertificateChunk7
import CertificateChunk8
import CertificateChunk9
import CertificateChunk10
import CertificateChunk11
import CertificateChunk12
import CertificateChunk13
import CertificateChunk14
import CertificateChunk15
import CertificateChunk16
import CertificateChunk17
import CertificateChunk18
import CertificateChunk19
import CertificateChunk20
import CertificateChunk21
import CertificateChunk22
import CertificateChunk23
import CertificateChunk24
import CertificateChunk25
import CertificateChunk26
import CertificateChunk27
import CertificateChunk28
import CertificateChunk29
import CertificateChunk30
import CertificateChunk31
import CertificateChunk32
import CertificateChunk33
import CertificateChunk34
import CertificateChunk35
import CertificateChunk36
import CertificateChunk37
import CertificateChunk38
import CertificateChunk39
import CertificateChunk40
import CertificateChunk41
import CertificateChunk42
import CertificateChunk43
import CertificateChunk44
import CertificateChunk45
import CertificateChunk46
import CertificateChunk47
import CertificateChunk48
import CertificateChunk49
import CertificateChunk50
import CertificateChunk51
import CertificateChunk52
import CertificateChunk53
import CertificateChunk54
import CertificateChunk55
import CertificateChunk56
import CertificateChunk57
import CertificateChunk58
import CertificateChunk59
import CertificateChunk60
import CertificateChunk61
import CertificateChunk62
import CertificateChunk63
import CertificateChunk64
import CertificateChunk65
import CertificateChunk66
import CertificateChunk67
import CertificateChunk68
import CertificateChunk69
import CertificateChunk70
import CertificateChunk71
import CertificateChunk72
import CertificateChunk73
import CertificateChunk74
import CertificateChunk75
import CertificateChunk76
import CertificateChunk77
import CertificateChunk78
import CertificateChunk79
import CertificateChunk80
import CertificateChunk81
import CertificateChunk82
import CertificateChunk83
import CertificateChunk84
import CertificateChunk85
import CertificateChunk86
import CertificateChunk87
import CertificateChunk88
import CertificateChunk89
import CertificateChunk90
import CertificateChunk91
import CertificateChunk92
import CertificateChunk93
import CertificateChunk94
import CertificateChunk95
import CertificateChunk96
import CertificateChunk97
import CertificateChunk98

namespace Pool039Finite

theorem covered_6 : Covered (matchings 6 (List.range 12)) :=
  covered_6_of_branches
    (covered_of_checkRows certificate_chunk_0)
    (covered_of_checkRows certificate_chunk_1)
    (covered_of_checkRows certificate_chunk_2)
    (covered_of_checkRows certificate_chunk_3)
    (covered_of_checkRows certificate_chunk_4)
    (covered_of_checkRows certificate_chunk_5)
    (covered_of_checkRows certificate_chunk_6)
    (covered_of_checkRows certificate_chunk_7)
    (covered_of_checkRows certificate_chunk_8)
    (covered_of_checkRows certificate_chunk_9)
    (covered_of_checkRows certificate_chunk_10)
    (covered_of_checkRows certificate_chunk_11)
    (covered_of_checkRows certificate_chunk_12)
    (covered_of_checkRows certificate_chunk_13)
    (covered_of_checkRows certificate_chunk_14)
    (covered_of_checkRows certificate_chunk_15)
    (covered_of_checkRows certificate_chunk_16)
    (covered_of_checkRows certificate_chunk_17)
    (covered_of_checkRows certificate_chunk_18)
    (covered_of_checkRows certificate_chunk_19)
    (covered_of_checkRows certificate_chunk_20)
    (covered_of_checkRows certificate_chunk_21)
    (covered_of_checkRows certificate_chunk_22)
    (covered_of_checkRows certificate_chunk_23)
    (covered_of_checkRows certificate_chunk_24)
    (covered_of_checkRows certificate_chunk_25)
    (covered_of_checkRows certificate_chunk_26)
    (covered_of_checkRows certificate_chunk_27)
    (covered_of_checkRows certificate_chunk_28)
    (covered_of_checkRows certificate_chunk_29)
    (covered_of_checkRows certificate_chunk_30)
    (covered_of_checkRows certificate_chunk_31)
    (covered_of_checkRows certificate_chunk_32)
    (covered_of_checkRows certificate_chunk_33)
    (covered_of_checkRows certificate_chunk_34)
    (covered_of_checkRows certificate_chunk_35)
    (covered_of_checkRows certificate_chunk_36)
    (covered_of_checkRows certificate_chunk_37)
    (covered_of_checkRows certificate_chunk_38)
    (covered_of_checkRows certificate_chunk_39)
    (covered_of_checkRows certificate_chunk_40)
    (covered_of_checkRows certificate_chunk_41)
    (covered_of_checkRows certificate_chunk_42)
    (covered_of_checkRows certificate_chunk_43)
    (covered_of_checkRows certificate_chunk_44)
    (covered_of_checkRows certificate_chunk_45)
    (covered_of_checkRows certificate_chunk_46)
    (covered_of_checkRows certificate_chunk_47)
    (covered_of_checkRows certificate_chunk_48)
    (covered_of_checkRows certificate_chunk_49)
    (covered_of_checkRows certificate_chunk_50)
    (covered_of_checkRows certificate_chunk_51)
    (covered_of_checkRows certificate_chunk_52)
    (covered_of_checkRows certificate_chunk_53)
    (covered_of_checkRows certificate_chunk_54)
    (covered_of_checkRows certificate_chunk_55)
    (covered_of_checkRows certificate_chunk_56)
    (covered_of_checkRows certificate_chunk_57)
    (covered_of_checkRows certificate_chunk_58)
    (covered_of_checkRows certificate_chunk_59)
    (covered_of_checkRows certificate_chunk_60)
    (covered_of_checkRows certificate_chunk_61)
    (covered_of_checkRows certificate_chunk_62)
    (covered_of_checkRows certificate_chunk_63)
    (covered_of_checkRows certificate_chunk_64)
    (covered_of_checkRows certificate_chunk_65)
    (covered_of_checkRows certificate_chunk_66)
    (covered_of_checkRows certificate_chunk_67)
    (covered_of_checkRows certificate_chunk_68)
    (covered_of_checkRows certificate_chunk_69)
    (covered_of_checkRows certificate_chunk_70)
    (covered_of_checkRows certificate_chunk_71)
    (covered_of_checkRows certificate_chunk_72)
    (covered_of_checkRows certificate_chunk_73)
    (covered_of_checkRows certificate_chunk_74)
    (covered_of_checkRows certificate_chunk_75)
    (covered_of_checkRows certificate_chunk_76)
    (covered_of_checkRows certificate_chunk_77)
    (covered_of_checkRows certificate_chunk_78)
    (covered_of_checkRows certificate_chunk_79)
    (covered_of_checkRows certificate_chunk_80)
    (covered_of_checkRows certificate_chunk_81)
    (covered_of_checkRows certificate_chunk_82)
    (covered_of_checkRows certificate_chunk_83)
    (covered_of_checkRows certificate_chunk_84)
    (covered_of_checkRows certificate_chunk_85)
    (covered_of_checkRows certificate_chunk_86)
    (covered_of_checkRows certificate_chunk_87)
    (covered_of_checkRows certificate_chunk_88)
    (covered_of_checkRows certificate_chunk_89)
    (covered_of_checkRows certificate_chunk_90)
    (covered_of_checkRows certificate_chunk_91)
    (covered_of_checkRows certificate_chunk_92)
    (covered_of_checkRows certificate_chunk_93)
    (covered_of_checkRows certificate_chunk_94)
    (covered_of_checkRows certificate_chunk_95)
    (covered_of_checkRows certificate_chunk_96)
    (covered_of_checkRows certificate_chunk_97)
    (covered_of_checkRows certificate_chunk_98)

#print axioms covered_6
end Pool039Finite
```

### `MaskSemantics.lean`

```lean
import EndpointTransport
set_option maxHeartbeats 0
namespace Pool039Finite
open Pool039

def maskColor : ℕ → ℕ → Bool
  | m, 0 => m % 2 == 1
  | m, i+1 => maskColor (m/2) i

theorem cross_eq_true (a b : Arc) : cross a b = true ↔
    Pool039.Cross ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ := by simp [cross, Pool039.Cross, and_assoc]

theorem nest_eq_true (a b : Arc) : nest a b = true ↔
    Pool039.Nest ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ := by simp [nest, Pool039.Nest]

theorem firstGood_sound (a : Arc) (q : Bool) (E : List Arc) (m : ℕ)
    (h : firstGood a q E m = true) : ∀ j : Fin E.length,
      (Pool039.Cross ⟨a.1,a.2⟩ (rowArc E j) → q = true ∨ maskColor m j.val = true) ∧
      (Pool039.Nest ⟨a.1,a.2⟩ (rowArc E j) → q = false ∨ maskColor m j.val = false) := by
  induction E generalizing m with
  | nil => intro j; exact Fin.elim0 j
  | cons b E ih =>
    have hh := Bool.and_eq_true_iff.mp h
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · cases q
      · constructor
        · intro hab
          have hc : m % 2 = 1 ∨ cross a b = false := by simpa using hh.1
          have hcross : cross a b = true := (cross_eq_true a b).mpr hab
          have hm : m % 2 = 1 := hc.resolve_right (by simp [hcross])
          simp [maskColor, hm]
        · intro _; simp
      · constructor
        · intro _; simp
        · intro hab
          have hn : m % 2 = 0 ∨ nest a b = false := by simpa using hh.1
          have hnest : nest a b = true := (nest_eq_true a b).mpr hab
          have hm : m % 2 = 0 := hn.resolve_right (by simp [hnest])
          simp [maskColor, hm]
    · simpa [rowArc, maskColor] using ih (m/2) hh.2 j

theorem goodMask_valid (E : List Arc) (m : ℕ) (h : goodMask E m = true) :
    ∀ i j : Fin E.length,
      (Pool039.Cross (rowArc E i) (rowArc E j) →
        maskColor m i.val = true ∨ maskColor m j.val = true) ∧
      (Pool039.Nest (rowArc E i) (rowArc E j) →
        maskColor m i.val = false ∨ maskColor m j.val = false) := by
  induction E generalizing m with
  | nil => intro i; exact Fin.elim0 i
  | cons a E ih =>
    have hh := Bool.and_eq_true_iff.mp h
    have hf := firstGood_sound a (m%2==1) E (m/2) hh.1
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨fun h => (cross_irrefl _ h).elim, fun h => (nest_irrefl _ h).elim⟩
      · simpa [rowArc, maskColor] using hf j
    · refine Fin.cases ?_ (fun j => ?_) j
      · have h := hf i
        constructor
        · intro hc
          exact (h.1 (cross_symm hc)).symm
        · intro hn
          exact (h.2 (nest_symm hn)).symm
      · simpa [rowArc, maskColor] using ih (m/2) hh.2 i j

theorem goodMask_sound (E : List Arc) (m : ℕ) (h : goodMask E m = true) : RowColor E :=
  ⟨fun i => maskColor m i.val, goodMask_valid E m h⟩

#print axioms goodMask_sound
end Pool039Finite
```

### `NormalizeSemantics.lean`

```lean
import EndpointTransport
import Mathlib.Tactic.SplitIfs

set_option maxHeartbeats 0
namespace Pool039Finite
open Pool039

def below (L : List ℕ) (x : ℕ) : ℕ := (L.filter (· < x)).length

theorem below_mono (L : List ℕ) {x y : ℕ} (hxy : x ≤ y) : below L x ≤ below L y := by
  induction L with
  | nil => simp [below]
  | cons a L ih =>
    simp only [below] at ih
    simp only [below, List.filter_cons]
    split_ifs <;> simp_all only [List.length_cons, decide_eq_true_eq] <;> omega

theorem below_strict (L : List ℕ) {x y : ℕ} (hx : x ∈ L) (hxy : x < y) :
    below L x < below L y := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · have hh := below_mono L (Nat.le_of_lt hxy)
      simp [below, hxy] at hh ⊢
      omega
    · have hh := ih hx
      simp only [below] at hh
      simp only [below, List.filter_cons]
      split_ifs <;> simp_all only [List.length_cons, decide_eq_true_eq] <;> omega

theorem below_lt_iff (L : List ℕ) {x y : ℕ} (hx : x ∈ L) :
    below L x < below L y ↔ x < y := by
  constructor
  · intro h
    by_contra hxy
    have hh := below_mono L (Nat.le_of_not_gt hxy)
    omega
  · exact below_strict L hx

theorem normalize_length (E : List Arc) : (normalize E).length = E.length := List.length_map _

theorem normalize_endpoint (E : List Arc) (i : Fin (normalize E).length) (s : Bool) :
    endpt (rowArc (normalize E) i) s =
      below (endpoints E) (endpt (rowArc E ⟨i.val, by simpa [normalize_length] using i.isLt⟩) s) := by
  unfold normalize at i
  cases s <;> simp [rowArc, normalize, endpt, below, endpoints]

theorem endpoint_mem (E : List Arc) (i : Fin E.length) (s : Bool) :
    endpt (rowArc E i) s ∈ endpoints E := by
  apply mem_endpoints.mpr
  refine ⟨E[i], ?_, ?_⟩
  · exact List.getElem_mem _
  · cases s
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem normalize_comparison (E : List Arc) (i j : Fin (normalize E).length) (s t : Bool) :
    endpt (rowArc (normalize E) i) s < endpt (rowArc (normalize E) j) t ↔
    endpt (rowArc E ⟨i.val, by simpa [normalize_length] using i.isLt⟩) s <
      endpt (rowArc E ⟨j.val, by simpa [normalize_length] using j.isLt⟩) t := by
  rw [normalize_endpoint, normalize_endpoint]
  apply below_lt_iff
  exact endpoint_mem E _ s

theorem select_sublist (E : List Arc) (m : ℕ) : (select E m).Sublist E := by
  induction E generalizing m with
  | nil => exact List.Sublist.refl _
  | cons a E ih =>
    simp only [select]
    split
    · exact (ih (m/2)).cons_cons a
    · exact (ih (m/2)).cons a

/-- A certificate selection has an injective edge map, even when list values repeat. -/
theorem normalized_selection_contains (E : List Arc) (m : ℕ) :
    RowContains E ((normalize (select E m)).map (fun p => (⟨p.1,p.2⟩ : Pool039.Arc))) := by
  let F := select E m
  obtain ⟨f,hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp (select_sublist E m)
  let castN : Fin (normalize F).length → Fin F.length :=
    fun i => ⟨i.val, by simpa only [normalize_length] using i.isLt⟩
  let castP : Fin ((normalize F).map (fun p => (⟨p.1,p.2⟩ : Pool039.Arc))).length →
      Fin (normalize F).length := fun i => ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  refine ⟨fun i => f (castN (castP i)), ?_, ?_⟩
  · intro i j he
    apply Fin.ext
    simpa only [castN, castP] using congrArg Fin.val (f.injective he)
  · intro i j s t
    have h := normalize_comparison F (castP i) (castP j) s t
    have hi : rowArc F (castN (castP i)) = rowArc E (f (castN (castP i))) := by
      have hh := hf (castN (castP i))
      change (⟨(F.get _).1,(F.get _).2⟩ : Pool039.Arc) = _
      rw [hh]
      rfl
    have hj : rowArc F (castN (castP j)) = rowArc E (f (castN (castP j))) := by
      have hh := hf (castN (castP j))
      change (⟨(F.get _).1,(F.get _).2⟩ : Pool039.Arc) = _
      rw [hh]
      rfl
    change _ ↔ endpt (rowArc E (f (castN (castP i)))) s < endpt (rowArc E (f (castN (castP j)))) t
    rw [← hi, ← hj]
    convert h using 1
    · simp only [Fin.getElem_fin, List.getElem_map]
      rfl

#print axioms normalized_selection_contains
end Pool039Finite
```

### `CertificateSemantics.lean`

```lean
import MaskSemantics
import NormalizeSemantics
import CertificateCoverageDefs

set_option maxHeartbeats 0
namespace Pool039Finite
open Pool039

def toSourceArcs (E : List Arc) : List Pool039.Arc := E.map (fun p => ⟨p.1,p.2⟩)

theorem sourceSQ_literal : sourceSQ.map toSourceArcs = Pool039.fig19a := by decide +kernel

theorem checkRow_sound (E : List Arc) (code : ℕ) (h : checkRow E code = true) :
    RowColor E ∨ ∃ P ∈ Pool039.fig19a, RowContains E P := by
  unfold checkRow at h
  split at h
  · exact Or.inl (goodMask_sound E _ h)
  · have hm : normalize (select E (code/2)) ∈ sourceSQ := List.mem_of_elem_eq_true h
    refine Or.inr ⟨toSourceArcs (normalize (select E (code/2))), ?_, ?_⟩
    · rw [← sourceSQ_literal]
      exact List.mem_map.mpr ⟨_,hm,rfl⟩
    · exact normalized_selection_contains E (code/2)

theorem covered_sound {rows} (h : Covered rows) {E} (hE : E ∈ rows) :
    RowColor E ∨ ∃ P ∈ Pool039.fig19a, RowContains E P := by
  obtain ⟨c,hc⟩ := h E hE
  exact checkRow_sound E c hc

#print axioms checkRow_sound
end Pool039Finite
```

### `Heredity.lean`

```lean
import EndpointTransport
set_option maxHeartbeats 0
namespace Pool039
variable {ι : Type} (M : OrderedMatching ι)

theorem contains_hasSQ (hM : M.HasColor) {P : List Arc} (hP : Contains M P) : HasSQ P := by
  obtain ⟨q,hq⟩ := hM
  obtain ⟨f,_,hcomp⟩ := hP
  have hc := comparisons_cross (fun i : Fin P.length => P[i]) (fun i => M.arc (f i)) hcomp
  have hn := comparisons_nest (fun i : Fin P.length => P[i]) (fun i => M.arc (f i)) hcomp
  refine ⟨fun i => q (f i),fun i j => ⟨?_,?_⟩⟩
  · intro hi hj hC
    have h := (hq (f i) (f j)).1 ((hc i j).mp hC)
    simp [hi,hj] at h
  · intro hi hj hN
    have h := (hq (f i) (f j)).2 ((hn i j).mp hN)
    simp [hi,hj] at h

theorem contains_onePage (hM : OneMixedPage M) {P : List Arc} (hP : Contains M P) : OnePage P := by
  obtain ⟨f,_,hcomp⟩ := hP
  rcases hM with hc | hn
  · exact Or.inl (fun i j h => hc (f i) (f j)
      ((comparisons_cross _ _ hcomp i j).mp h))
  · exact Or.inr (fun i j h => hn (f i) (f j)
      ((comparisons_nest _ _ hcomp i j).mp h))

#print axioms contains_hasSQ
#print axioms contains_onePage
end Pool039
```

### `SourceObstructions.lean`

```lean
import Heredity

set_option maxHeartbeats 0
namespace Pool039

theorem fig19a_uncolourable : ∀ P ∈ fig19a, ¬ HasSQ P := by
  intro P hP
  simp only [fig19a, sourceSQ, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

theorem fig19b_not_onePage : ∀ P ∈ fig19b, ¬ OnePage P := by
  intro P hP
  simp only [fig19b, sourceOne, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

theorem sq_avoids {ι : Type} (M : OrderedMatching ι) (h : OneStackOneQueue M) :
    ∀ P ∈ fig19a, ¬Contains M P := by
  intro P hP hc
  exact fig19a_uncolourable P hP (contains_hasSQ M (M.oneStackOneQueue_iff_hasColor.mp h) hc)

theorem one_avoids {ι : Type} (M : OrderedMatching ι) (h : OneMixedPage M) :
    ∀ P ∈ fig19b, ¬Contains M P := by
  intro P hP hc
  exact fig19b_not_onePage P hP (contains_onePage M h hc)

#print axioms fig19a_uncolourable
#print axioms fig19b_not_onePage
#print axioms sq_avoids
#print axioms one_avoids
end Pool039
```

### `OnePageCore.lean`

```lean
import EndpointTransport
set_option maxHeartbeats 0
namespace Pool039

def RowOne (E : List Pool039Finite.Arc) : Prop :=
  (∀ i j, ¬Cross (rowArc E i) (rowArc E j)) ∨
  (∀ i j, ¬Nest (rowArc E i) (rowArc E j))

namespace OrderedMatching
variable {ι : Type} (M : OrderedMatching ι)

theorem presents_one {E} (h : Presents M E) : RowOne E ↔ OneMixedPage M := by
  obtain ⟨e,he⟩ := h
  have hc := comparisons_cross (rowArc E) (fun i => M.arc (e i)) he
  have hn := comparisons_nest (rowArc E) (fun i => M.arc (e i)) he
  constructor
  · rintro (h | h)
    · exact Or.inl (fun a b hab => h (e.symm a) (e.symm b) ((hc _ _).mpr (by simpa using hab)))
    · exact Or.inr (fun a b hab => h (e.symm a) (e.symm b) ((hn _ _).mpr (by simpa using hab)))
  · rintro (h | h)
    · exact Or.inl (fun a b hab => h (e a) (e b) ((hc _ _).mp hab))
    · exact Or.inr (fun a b hab => h (e a) (e b) ((hn _ _).mp hab))

theorem four_edge_one_core (h : ¬ OneMixedPage M) :
    ∃ H : Finset ι, H.card ≤ 4 ∧ ¬ OneMixedPage (M.restrict H) := by
  classical
  have hc : ∃ a b, Cross (M.arc a) (M.arc b) := by
    by_contra hn
    exact h (Or.inl (by simpa using hn))
  have hn : ∃ c d, Nest (M.arc c) (M.arc d) := by
    by_contra hn
    exact h (Or.inr (by simpa using hn))
  obtain ⟨a,b,hab⟩ := hc
  obtain ⟨c,d,hcd⟩ := hn
  let H := ([a,b,c,d] : List ι).toFinset
  refine ⟨H, ?_, ?_⟩
  · simpa only [H, List.length_cons, List.length_nil] using (List.toFinset_card_le (l := [a,b,c,d]))
  · let aa : {i // i ∈ H} := ⟨a,by simp [H]⟩
    let bb : {i // i ∈ H} := ⟨b,by simp [H]⟩
    let cc : {i // i ∈ H} := ⟨c,by simp [H]⟩
    let dd : {i // i ∈ H} := ⟨d,by simp [H]⟩
    rintro (hc | hn)
    · exact hc aa bb hab
    · exact hn cc dd hcd

theorem enumerated_bad_one_core [Fintype ι] (h : ¬ OneMixedPage M) :
    ∃ m ≤ 4, ∃ E ∈ Pool039Finite.matchings m (List.range (2*m)),
      ¬ RowOne E ∧ ∀ P, RowContains E P → Contains M P := by
  classical
  obtain ⟨H,hcard,hbad⟩ := M.four_edge_one_core h
  obtain ⟨E,hE,_,hp,_,hcont⟩ := (M.restrict H).enumerated_presentation
  refine ⟨H.card,hcard,E,?_,fun he => hbad (((M.restrict H).presents_one hp).mp he),?_⟩
  · simpa using hE
  · intro P hP
    obtain ⟨f,hf,hcmp⟩ := (hcont P).mp hP
    exact ⟨fun i => (f i).val, Subtype.val_injective.comp hf, hcmp⟩

#print axioms enumerated_bad_one_core
end OrderedMatching
end Pool039
```

### `OneCertificateDefs.lean`

```lean
import CertificateSemantics
import OnePageCore
set_option maxHeartbeats 0
namespace Pool039Finite
open Pool039

def sourceOnePairs : List (List Arc) := [[(0,4),(1,3),(2,5)],[(0,2),(1,5),(3,4)],[(0,5),(1,3),(2,4)],[(0,2),(1,3),(4,7),(5,6)],[(0,3),(1,5),(2,4)],[(0,4),(1,2),(3,5)],[(0,4),(1,5),(2,3)],[(0,3),(1,2),(4,6),(5,7)]]

def oneFree (E : List Arc) (q : Bool) : Bool :=
  E.all (fun a => E.all (fun b => !(if q then nest a b else cross a b)))

def oneCheck (E : List Arc) (code : ℕ) : Bool :=
  if code % 2 = 0 then oneFree E (code/2 == 1)
  else sourceOnePairs.contains (normalize (select E (code/2)))

def oneRows : List (List Arc) → List ℕ → Bool
  | [], [] => true
  | E::es, c::cs => oneCheck E c && oneRows es cs
  | _, _ => false

theorem sourceOne_literal : sourceOnePairs.map toSourceArcs = Pool039.fig19b := by decide +kernel
end Pool039Finite
```

### `OneCertificate0.lean`

```lean
import OneCertificateDefs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Pool039Finite
def oneCodes0 : List ℕ := [0]
theorem one_certificate0 : oneRows (matchings 0 (List.range 0)) oneCodes0 = true := by decide +kernel
#print axioms one_certificate0
end Pool039Finite
```

### `OneCertificate1.lean`

```lean
import OneCertificateDefs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Pool039Finite
def oneCodes1 : List ℕ := [0]
theorem one_certificate1 : oneRows (matchings 1 (List.range 2)) oneCodes1 = true := by decide +kernel
#print axioms one_certificate1
end Pool039Finite
```

### `OneCertificate2.lean`

```lean
import OneCertificateDefs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Pool039Finite
def oneCodes2 : List ℕ := [0,2,0]
theorem one_certificate2 : oneRows (matchings 2 (List.range 4)) oneCodes2 = true := by decide +kernel
#print axioms one_certificate2
end Pool039Finite
```

### `OneCertificate3.lean`

```lean
import OneCertificateDefs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Pool039Finite
def oneCodes3 : List ℕ := [0,2,0,2,2,15,0,2,15,15,15,15,0,15,0]
theorem one_certificate3 : oneRows (matchings 3 (List.range 6)) oneCodes3 = true := by decide +kernel
#print axioms one_certificate3
end Pool039Finite
```

### `OneCertificate4.lean`

```lean
import OneCertificateDefs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Pool039Finite
def oneCodes4 : List ℕ := [0,2,0,2,2,29,0,2,29,29,29,29,0,29,0,2,2,31,2,2,29,15,2,29,15,15,23,15,15,15,0,31,0,2,2,27,15,2,27,15,15,23,15,15,15,15,15,15,15,15,15,15,2,27,15,15,23,15,15,15,0,15,15,15,15,15,0,15,15,15,15,23,15,15,15,23,23,15,15,15,15,23,15,15,23,23,15,15,15,15,0,27,0,15,15,15,0,15,15,23,23,15,0,27,0]
theorem one_certificate4 : oneRows (matchings 4 (List.range 8)) oneCodes4 = true := by decide +kernel
#print axioms one_certificate4
end Pool039Finite
```

### `OneCertificateSemantics.lean`

```lean
import OneCertificateDefs
set_option maxHeartbeats 0
namespace Pool039Finite
open Pool039

theorem oneFree_sound (E : List Arc) (q : Bool) (h : oneFree E q = true) : RowOne E := by
  have hf : ∀ a ∈ E, ∀ b ∈ E, (if q then nest a b else cross a b) = false := by
    simpa [oneFree, List.all_eq_true] using h
  cases q
  · apply Or.inl
    intro i j hc
    have hh := hf E[i] (List.getElem_mem _) E[j] (List.getElem_mem _)
    have hc' := (cross_eq_true E[i] E[j]).mpr hc
    exact Bool.noConfusion (hc'.symm.trans hh)
  · apply Or.inr
    intro i j hn
    have hh := hf E[i] (List.getElem_mem _) E[j] (List.getElem_mem _)
    have hn' := (nest_eq_true E[i] E[j]).mpr hn
    exact Bool.noConfusion (hn'.symm.trans hh)

theorem oneCheck_sound (E : List Arc) (code : ℕ) (h : oneCheck E code = true) :
    RowOne E ∨ ∃ P ∈ Pool039.fig19b, RowContains E P := by
  unfold oneCheck at h
  split at h
  · exact Or.inl (oneFree_sound E _ h)
  · have hm : normalize (select E (code/2)) ∈ sourceOnePairs := List.mem_of_elem_eq_true h
    refine Or.inr ⟨toSourceArcs (normalize (select E (code/2))), ?_, ?_⟩
    · rw [← sourceOne_literal]
      exact List.mem_map.mpr ⟨_,hm,rfl⟩
    · exact normalized_selection_contains E (code/2)

theorem oneRows_sound {rows codes} (h : oneRows rows codes = true) :
    ∀ E ∈ rows, RowOne E ∨ ∃ P ∈ Pool039.fig19b, RowContains E P := by
  induction rows generalizing codes with
  | nil => simp
  | cons E rows ih =>
    cases codes with
    | nil => simp [oneRows] at h
    | cons c codes =>
      have hh := Bool.and_eq_true_iff.mp h
      intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact oneCheck_sound _ c hh.1
      · exact ih hh.2 F hF

#print axioms oneCheck_sound
end Pool039Finite
```

### `OnePageTheorem.lean`

```lean
import OneCertificateSemantics
import OneCertificate0
import OneCertificate1
import OneCertificate2
import OneCertificate3
import OneCertificate4
import SourceObstructions
set_option maxHeartbeats 0
namespace Pool039Finite
open Pool039

theorem one_finite (n : ℕ) (hn : n ≤ 4) {E : List Arc}
    (hE : E ∈ matchings n (List.range (2*n))) :
    RowOne E ∨ ∃ P ∈ Pool039.fig19b, RowContains E P := by
  have he : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact oneRows_sound one_certificate0 E hE
  · exact oneRows_sound one_certificate1 E hE
  · exact oneRows_sound one_certificate2 E hE
  · exact oneRows_sound one_certificate3 E hE
  · exact oneRows_sound one_certificate4 E hE
end Pool039Finite

namespace Pool039

theorem onePage_characterization {ι : Type} [Fintype ι] (M : OrderedMatching ι) :
    OneMixedPage M ↔ ∀ P ∈ fig19b, ¬ Contains M P := by
  constructor
  · exact one_avoids M
  · intro h
    by_contra hn
    obtain ⟨m,hm,E,hE,hbad,htransfer⟩ := M.enumerated_bad_one_core hn
    rcases Pool039Finite.one_finite m hm hE with hc | ⟨P,hP,hc⟩
    · exact hbad hc
    · exact h P hP (htransfer P hc)

#print axioms onePage_characterization
end Pool039
```

### `FiniteClassification.lean`

```lean
import CoverageSmall
import CoverageSix
import CertificateSemantics
set_option maxHeartbeats 0
namespace Pool039Finite
open Pool039

theorem sq_finite (n : ℕ) (hn : n ≤ 6) {E : List Arc}
    (hE : E ∈ matchings n (List.range (2*n))) :
    RowColor E ∨ ∃ P ∈ Pool039.fig19a, RowContains E P := by
  have he : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact covered_sound covered_0 hE
  · exact covered_sound covered_1 hE
  · exact covered_sound covered_2 hE
  · exact covered_sound covered_3 hE
  · exact covered_sound covered_4 hE
  · exact covered_sound covered_5 hE
  · exact covered_sound covered_6 hE

#print axioms sq_finite
end Pool039Finite
```

### `Conjecture31.lean`

```lean
import FiniteClassification
import OnePageTheorem
set_option maxHeartbeats 0
namespace Pool039

theorem sq_characterization {ι : Type} [Fintype ι] (M : OrderedMatching ι) :
    OneStackOneQueue M ↔ ∀ P ∈ fig19a, ¬ Contains M P := by
  constructor
  · exact sq_avoids M
  · intro h
    apply M.oneStackOneQueue_iff_hasColor.mpr
    by_contra hn
    obtain ⟨m,hm,E,hE,hbad,htransfer⟩ := M.enumerated_bad_core hn
    rcases Pool039Finite.sq_finite m hm hE with hc | ⟨P,hP,hc⟩
    · exact hbad hc
    · exact h P hP (htransfer P hc)

/-- Conjecture 31 of Haun, Merker and Pupyrev, arXiv:2412.12786v2.
No size bound, criticality, normalization or certificate assumption occurs here. -/
theorem haun_merker_pupyrev_conj31 {ι : Type} [Fintype ι] (M : OrderedMatching ι) :
    (OneStackOneQueue M ↔ ∀ P ∈ fig19a, ¬Contains M P) ∧
    (OneMixedPage M ↔ ∀ P ∈ fig19b, ¬Contains M P) :=
  ⟨sq_characterization M, onePage_characterization M⟩

/-- A concrete inhabitant witnesses satisfiability of the matching hypotheses. -/
def emptyMatching : OrderedMatching (Fin 0) where
  arc i := Fin.elim0 i
  proper i := Fin.elim0 i
  apart i := Fin.elim0 i

theorem empty_layouts : OneStackOneQueue emptyMatching ∧ OneMixedPage emptyMatching := by
  constructor
  · exact ⟨fun _ => false, fun a => Fin.elim0 a⟩
  · exact Or.inl (fun a => Fin.elim0 a)

#print haun_merker_pupyrev_conj31
#print axioms sq_characterization
#print axioms onePage_characterization
#print axioms haun_merker_pupyrev_conj31
end Pool039
```

### `EndpointAudit.lean`

```lean
import Conjecture31
namespace Pool039
#eval Lean.versionString
#print OrderedMatching
#print OneStackOneQueue
#print OneMixedPage
#print Contains
#print endpt
#print fig19a
#print fig19b
#check OrderedMatching.enumerated_presentation
#check OrderedMatching.enumerated_bad_core
#check OrderedMatching.enumerated_bad_one_core
#check sq_characterization
#check onePage_characterization
#check haun_merker_pupyrev_conj31
#print axioms sq_characterization
#print axioms onePage_characterization
#print axioms haun_merker_pupyrev_conj31
#print axioms empty_layouts
end Pool039
```

