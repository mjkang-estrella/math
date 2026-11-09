import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace R212
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def facet (i : Fin 9) : Finset ℕ :=
  match i.val with
  | 0 => {0,1,2,3}
  | 1 => {1,2,3,4}
  | 2 => {1,2,3,5}
  | 3 => {1,3,5,6}
  | 4 => {1,4,5,6}
  | 5 => {1,4,5,7}
  | 6 => {0,1,4,7}
  | 7 => {0,4,6,7}
  | _ => {8,9,10,11}

def faces : Finset (Finset ℕ) := Finset.univ.biUnion fun i : Fin 9 => (facet i).powerset

def alpha (k : ℕ) : ℕ := (faces.filter fun s => s.card = k + 1).card

theorem face_counts : (alpha 0, alpha 1, alpha 2, alpha 3) = (12,30,29,9) := by
  decide +kernel

theorem pure_facets : ∀ i : Fin 9, (facet i).card = 4 := by decide +kernel

def LaterRidgeUnique : Prop := ∀ i j k : Fin 9, i < j → i < k →
  ∀ a ∈ (facet i).powersetCard 3, ∀ b ∈ (facet i).powersetCard 3,
  a ⊆ facet j → b ⊆ facet k → a = b

def parentRidge (i : Fin 9) : Finset ℕ :=
 match i.val with
 | 0 | 1 => {1,2,3}
 | 2 => {1,3,5}
 | 3 => {1,5,6}
 | 4 => {1,4,5}
 | 5 => {1,4,7}
 | 6 => {0,4,7}
 | _ => ∅

theorem parent_card : ∀ i : Fin 9, (parentRidge i).card ≤ 3 := by decide +kernel

theorem intersections : ∀ i j : Fin 9, i < j →
 (facet i ∩ facet j).card ≤ 2 ∨ facet i ∩ facet j = parentRidge i := by decide +kernel

theorem ridge_parent (i j : Fin 9) (hij : i < j) (a : Finset ℕ)
 (ha : a ∈ (facet i).powersetCard 3) (hj : a ⊆ facet j) : a = parentRidge i := by
 rw [Finset.mem_powersetCard] at ha
 have hsub : a ⊆ facet i ∩ facet j := Finset.subset_inter ha.1 hj
 rcases intersections i j hij with hsmall | heq
 · have hcard := Finset.card_le_card hsub
   omega
 · rw [heq] at hsub
   exact Finset.eq_of_subset_of_card_le hsub (by simpa [ha.2] using parent_card i)

theorem laterRidgeUnique : LaterRidgeUnique := by
 intro i j k hij hik a ha b hb haj hbk
 exact (ridge_parent i j hij a ha haj).trans (ridge_parent i k hik b hb hbk).symm

/-- An abstract cyclic facet/ridge sequence. This allows multiple cyclic orbits,
so absence of these sequences is stronger than absence of a single circuit. -/
def Circuit (r : ℕ) (next : Equiv.Perm (Fin r)) (f : Fin r → Fin 9)
    (s : Fin r → Finset ℕ) : Prop :=
  0 < r ∧ (∀ i, next i ≠ i) ∧ Function.Injective f ∧ Function.Injective s ∧
  (∀ i, (s i).card = 3) ∧ (∀ i, s i ⊆ facet (f i)) ∧
  (∀ i, s i ⊆ facet (f (next i)))

theorem no_circuit (r : ℕ) (next : Equiv.Perm (Fin r))
    (f : Fin r → Fin 9) (s : Fin r → Finset ℕ) : ¬ Circuit r next f s := by
  rintro ⟨hr, hn, hf, hs, hc, hsub, hadj⟩
  let : NeZero r := ⟨by omega⟩
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have hmin' : ∀ j, f i ≤ f j := fun j => hmin j (Finset.mem_univ j)
  have hnext : f i < f (next i) := lt_of_le_of_ne (hmin' _) (hf.ne (hn i).symm)
  have hprevne : next.symm i ≠ i := by
    intro h
    have : next i = i := by simpa [h] using next.apply_symm_apply i
    exact hn i this
  have hprev : f i < f (next.symm i) :=
    lt_of_le_of_ne (hmin' _) (hf.ne hprevne.symm)
  have ha : s i ∈ (facet (f i)).powersetCard 3 := by
    simpa only [Finset.mem_powersetCard] using And.intro (hsub i) (hc i)
  have hb : s (next.symm i) ∈ (facet (f i)).powersetCard 3 := by
    rw [Finset.mem_powersetCard]
    exact ⟨by simpa using hadj (next.symm i), hc _⟩
  have heq := laterRidgeUnique (f i) (f (next i)) (f (next.symm i)) hnext hprev
    (s i) ha (s (next.symm i)) hb (hadj i) (hsub _)
  exact hprevne (hs heq).symm

#print axioms face_counts
#print axioms pure_facets
#print axioms laterRidgeUnique
#print axioms no_circuit
end R212

namespace R212

def ridges := faces.filter fun s => s.card = 3
abbrev Ridge := ↥ridges

def step (a b : Ridge) : Prop := ∃ i : Fin 9, a.val ⊆ facet i ∧ b.val ⊆ facet i
instance (a b : Ridge) : Decidable (step a b) := by unfold step; infer_instance

def side (a : Ridge) : Bool := decide ((a.val ∩ Finset.range 8).Nonempty)

theorem facet_side : ∀ i : Fin 9, ∀ a ∈ (facet i).powersetCard 3,
 decide ((a ∩ Finset.range 8).Nonempty) = decide (i.val < 8) := by decide +kernel

theorem step_side : ∀ a b : Ridge, step a b → side a = side b := by
 intro a b ⟨i, ha, hb⟩
 have hac : a.val.card = 3 := (Finset.mem_filter.mp a.property).2
 have hbc : b.val.card = 3 := (Finset.mem_filter.mp b.property).2
 exact (facet_side i a.val (by simpa only [Finset.mem_powersetCard] using And.intro ha hac)).trans
  (facet_side i b.val (by simpa only [Finset.mem_powersetCard] using And.intro hb hbc)).symm

theorem path_side {a b : Ridge} (h : Relation.ReflTransGen step a b) : side a = side b := by
  induction h with
  | refl => rfl
  | @tail b c h hbc ih => exact ih.trans (step_side b c hbc)

def a0 : Ridge := ⟨{0,1,2}, by decide⟩
def a1 : Ridge := ⟨{8,9,10}, by decide⟩

def Connected : Prop := ∀ a b : Ridge, Relation.ReflTransGen step a b

theorem not_connected : ¬ Connected := by
  intro h
  have heq := path_side (h a0 a1)
  have hneq : side a0 ≠ side a1 := by decide +kernel
  exact hneq heq

#print axioms step_side
#print axioms path_side
#print axioms not_connected
end R212
