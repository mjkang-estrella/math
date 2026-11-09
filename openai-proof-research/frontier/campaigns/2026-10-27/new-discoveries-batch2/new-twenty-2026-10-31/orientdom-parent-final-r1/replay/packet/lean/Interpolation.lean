import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

set_option linter.unusedSectionVars false
namespace OrientableTotalDomination
abbrev Rel (V : Type) := V → V → Bool
variable {V : Type} [Fintype V] [DecidableEq V]
def Arc (D : Rel V) (u v : V) : Prop := D u v = true
def Valid (D : Rel V) : Prop := ∀ v, ∃ u, Arc D u v
def Asym (D : Rel V) : Prop := ∀ u v, Arc D u v → ¬ Arc D v u
def Same (D E : Rel V) : Prop := ∀ u v, (Arc D u v ∨ Arc D v u) ↔ (Arc E u v ∨ Arc E v u)
def TD (D : Rel V) (S : Finset V) : Prop := ∀ v, ∃ u ∈ S, Arc D u v
def Minimum (D : Rel V) (S : Finset V) : Prop := TD D S ∧ ∀ T, TD D T → S.card ≤ T.card
noncomputable def flip (D : Rel V) (a b : V) : Rel V := fun u v =>
 if u = a ∧ v = b then false else if u = b ∧ v = a then true else D u v
noncomputable def diff (D E : Rel V) : Finset (V × V) := by
 classical
 exact Finset.univ.filter (fun e => Arc D e.1 e.2 ∧ ¬ Arc E e.1 e.2)

lemma minimum_exists (D : Rel V) (hD : Valid D) : ∃ S, Minimum D S := by
 classical
 have hex : ∃ k : ℕ, ∃ S : Finset V, TD D S ∧ S.card = k :=
  ⟨Fintype.card V, Finset.univ, by simpa [TD, Valid] using hD, by simp⟩
 obtain ⟨S, hS, hc⟩ := Nat.find_spec hex
 refine ⟨S, hS, ?_⟩
 intro T hT
 rw [hc]
 exact Nat.find_min' hex ⟨T, hT, rfl⟩

lemma safe_edge (D E : Rel V) (hE : Valid E) (hAsym : Asym E) (hSame : Same D E)
 (S : Finset V) (hS : TD D S) (hnot : ¬ TD E S) :
 ∃ a b w, Arc D a b ∧ ¬ Arc E a b ∧ Arc D w b ∧ w ≠ a := by
 classical
 by_contra hn
 push Not at hn
 have hforced : ∀ v, (∃ a, Arc D a v ∧ ¬ Arc E a v) → v ∈ S := by
  intro v hv
  obtain ⟨a, ha, hna⟩ := hv
  obtain ⟨w, hw⟩ := hE v
  have hwd : ¬ Arc D w v := by
   intro hd
   have heq := hn a v w ha hna hd
   subst w
   exact hna hw
  have hr : Arc D v w := ((hSame w v).mpr (Or.inl hw)).resolve_left hwd
  have hre : ¬ Arc E v w := hAsym w v hw
  obtain ⟨s,hs,hsd⟩ := hS w
  have heq := hn v w s hr hre hsd
  simpa [heq] using hs
 apply hnot
 intro v
 obtain ⟨a,ha,hav⟩ := hS v
 by_cases hae : Arc E a v
 · exact ⟨a,ha,hae⟩
 obtain ⟨w,hw⟩ := hE v
 have hwd : ¬ Arc D w v := by
  intro hd
  have heq := hn a v w hav hae hd
  subst w
  exact hae hw
 have hr : Arc D v w := ((hSame w v).mpr (Or.inl hw)).resolve_left hwd
 exact ⟨w,hforced w ⟨v,hr,hAsym w v hw⟩,hw⟩

lemma arc_flip (D : Rel V) (a b u v : V) (hne : a ≠ b) :
 Arc (flip D a b) u v ↔ (u = b ∧ v = a) ∨ (Arc D u v ∧ ¬ (u = a ∧ v = b)) := by
 classical
 simp only [Arc, flip]
 split_ifs <;> simp_all

lemma flip_asym (D : Rel V) (hD : Asym D) (a b : V) (hab : Arc D a b) :
 Asym (flip D a b) := by
 have hne : a ≠ b := by intro h; subst b; exact hD a a hab hab
 intro u v huv hvu
 rw [arc_flip D a b u v hne] at huv
 rw [arc_flip D a b v u hne] at hvu
 rcases huv with ⟨rfl, rfl⟩ | ⟨huv, huv'⟩
 · rcases hvu with h | h
   · exact hne h.1
   · exact h.2 ⟨rfl, rfl⟩
 · rcases hvu with ⟨rfl, rfl⟩ | ⟨hvu, _⟩
   · exact huv' ⟨rfl, rfl⟩
   · exact hD u v huv hvu

lemma flip_same (D : Rel V) (hD : Asym D) (a b : V) (hab : Arc D a b) :
 Same D (flip D a b) := by
 have hne : a ≠ b := by intro h; subst b; exact hD a a hab hab
 intro u v
 rw [arc_flip D a b u v hne, arc_flip D a b v u hne]
 constructor
 · intro h
   by_cases h1 : u = a ∧ v = b
   · rcases h1 with ⟨rfl, rfl⟩; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
   by_cases h2 : v = a ∧ u = b
   · rcases h2 with ⟨rfl, rfl⟩; exact Or.inl (Or.inl ⟨rfl, rfl⟩)
   rcases h with h | h
   · exact Or.inl (Or.inr ⟨h, h1⟩)
   · exact Or.inr (Or.inr ⟨h, h2⟩)
 · rintro ((⟨rfl, rfl⟩ | ⟨h, _⟩) | (⟨rfl, rfl⟩ | ⟨h, _⟩))
   · exact Or.inr hab
   · exact Or.inl h
   · exact Or.inl hab
   · exact Or.inr h

lemma flip_valid (D : Rel V) (hD : Asym D) (hv : Valid D)
 (a b w : V) (hab : Arc D a b) (hwb : Arc D w b) (hw : w ≠ a) :
 Valid (flip D a b) := by
 have hne : a ≠ b := by intro h; subst b; exact hD a a hab hab
 intro v
 by_cases h : v = b
 · subst v
   exact ⟨w, (arc_flip D a b w b hne).mpr (Or.inr ⟨hwb, by simp [hw]⟩)⟩
 · obtain ⟨u, hu⟩ := hv v
   exact ⟨u, (arc_flip D a b u v hne).mpr (Or.inr ⟨hu, by simp [h]⟩)⟩

lemma flip_td (D : Rel V) (hD : Asym D) (a b w : V) (hab : Arc D a b)
 (hwb : Arc D w b) (S : Finset V) (hS : TD D S) (hw : w ≠ a) :
 TD (flip D a b) (insert w S) := by
 classical
 have hne : a ≠ b := by intro h; subst b; exact hD a a hab hab
 intro v
 by_cases h : v = b
 · subst v
   exact ⟨w, Finset.mem_insert_self _ _, (arc_flip D a b w b hne).mpr (Or.inr ⟨hwb, by simp [hw]⟩)⟩
 · obtain ⟨u, hu, huv⟩ := hS v
   exact ⟨u, Finset.mem_insert_of_mem hu, (arc_flip D a b u v hne).mpr (Or.inr ⟨huv, by simp [h]⟩)⟩

lemma flip_decreases (D E : Rel V) (hD : Asym D) (hSame : Same D E)
 (a b : V) (hab : Arc D a b) (hnab : ¬ Arc E a b) :
 (diff (flip D a b) E).card < (diff D E).card := by
 classical
 have hne : a ≠ b := by intro h; subst b; exact hD a a hab hab
 have he : Arc E b a := ((hSame a b).mp (Or.inl hab)).resolve_left hnab
 apply Finset.card_lt_card
 apply Finset.ssubset_iff_subset_ne.mpr
 constructor
 · intro e hee
   simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and] at hee ⊢
   rcases (arc_flip D a b e.1 e.2 hne).mp hee.1 with ⟨h1,h2⟩ | ⟨h,_⟩
   · exact False.elim (hee.2 (by simpa [h1,h2] using he))
   · exact ⟨h, hee.2⟩
 · intro eq
   have hmem : (a,b) ∈ diff D E := by simp [diff,hab,hnab]
   rw [← eq] at hmem
   have hf : Arc (flip D a b) a b := (Finset.mem_filter.mp (show (a,b) ∈ Finset.univ.filter (fun e : V × V => Arc (flip D a b) e.1 e.2 ∧ ¬ Arc E e.1 e.2) from hmem)).2.1
   simp [Arc,flip] at hf

/-- Every integer between two attained total domination numbers is attained.
This brackets the lower and upper orientable total domination numbers. -/
theorem interpolation (D E : Rel V) (hD : Asym D) (hE : Asym E)
 (hvD : Valid D) (hvE : Valid E) (hSame : Same D E)
 (S T : Finset V) (hS : Minimum D S) (hT : Minimum E T)
 (c : ℕ) (hc : S.card ≤ c) (hcT : c ≤ T.card) :
 ∃ F : Rel V, Asym F ∧ Valid F ∧ Same D F ∧ ∃ U, Minimum F U ∧ U.card = c := by
 classical
 generalize hm : (diff D E).card = m
 induction m using Nat.strong_induction_on generalizing D S with
 | h m ih =>
   by_cases heq : S.card = c
   · exact ⟨D, hD, hvD, fun _ _ => Iff.rfl, S, hS, heq⟩
   have hlt : S.card < c := lt_of_le_of_ne hc heq
   have hnot : ¬ TD E S := by intro hs; have := hT.2 S hs; omega
   obtain ⟨a,b,w,hab,hnab,hwb,hw⟩ := safe_edge D E hvE hE hSame S hS.1 hnot
   let F := flip D a b
   have hF := flip_asym D hD a b hab
   have hvF := flip_valid D hD hvD a b w hab hwb hw
   have hsDF := flip_same D hD a b hab
   have hsFE : Same F E := fun u v => ((hsDF u v).symm).trans (hSame u v)
   obtain ⟨U,hU⟩ := minimum_exists F hvF
   have hUc : U.card ≤ c := by
    have hh := hU.2 (insert w S) (flip_td D hD a b w hab hwb S hS.1 hw)
    have hh' := Finset.card_insert_le w S
    omega
   have hdec : (diff F E).card < m := by rw [← hm]; exact flip_decreases D E hD hSame a b hab hnab
   obtain ⟨R,hrA,hrV,hrSame,W,hrW,hrc⟩ := ih (diff F E).card hdec F hF hvF hsFE U hU hUc rfl
   exact ⟨R,hrA,hrV,fun u v => (hsDF u v).trans (hrSame u v),W,hrW,hrc⟩

/-- Boolean adjacency representation of an orientation of the underlying graph. -/
def OrientationOf (G D : Rel V) : Prop :=
 Asym D ∧ ∀ u v, (Arc D u v ∨ Arc D v u) ↔ Arc G u v
/-- The finite set of total domination numbers of valid orientations. -/
noncomputable def spectrum (G : Rel V) : Finset ℕ := by
 classical
 exact (Finset.range (Fintype.card V + 1)).filter (fun k =>
  ∃ D : Rel V, OrientationOf G D ∧ Valid D ∧ ∃ S, Minimum D S ∧ S.card = k)
noncomputable def lower (G : Rel V) (h : (spectrum G).Nonempty) : ℕ := (spectrum G).min' h
noncomputable def upper (G : Rel V) (h : (spectrum G).Nonempty) : ℕ := (spectrum G).max' h

/-- Literal general intermediate-value assertion for all finite graphs admitting
valid orientations, with the lower and upper numbers defined as actual extrema. -/
def Conjecture : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V]
 (G : Rel V) (h : (spectrum G).Nonempty) (c : ℕ),
 lower G h ≤ c → c ≤ upper G h → c ∈ spectrum G

theorem conjecture_true : Conjecture := by
 classical
 intro V _ _ G h c hlo hhi
 have hmin := Finset.min'_mem (spectrum G) h
 have hmax := Finset.max'_mem (spectrum G) h
 obtain ⟨D, hD, hvD, S, hS, hcS⟩ := (Finset.mem_filter.mp hmin).2
 obtain ⟨E, hE, hvE, T, hT, hcT⟩ := (Finset.mem_filter.mp hmax).2
 have hs : Same D E := fun u v => (hD.2 u v).trans (hE.2 u v).symm
 obtain ⟨F,hf,hvf,hsf,U,hu,huc⟩ := interpolation D E hD.1 hE.1 hvD hvE hs S T hS hT c
  (by simpa [lower, hcS] using hlo) (by simpa [upper, hcT] using hhi)
 apply Finset.mem_filter.mpr
 constructor
 · apply Finset.mem_range.mpr
   have hh := Finset.card_le_univ U
   omega
 · exact ⟨F,⟨hf,fun u v => ((hsf u v).symm).trans (hD.2 u v)⟩,hvf,U,hu,huc⟩
#print axioms conjecture_true
#print axioms interpolation
end OrientableTotalDomination
