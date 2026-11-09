import Bridge
import Mathlib.Combinatorics.SimpleGraph.Diam
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
namespace Circulant350979

def MonophonicSet {α : Type} (R : α → α → Prop) (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → TripleMP R a b c

noncomputable def mpNumber {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) : ℕ := by
  classical
  exact (Finset.univ.filter (MonophonicSet G.Adj)).sup Finset.card

lemma mp_triple {α : Type} [DecidableEq α] {R : α → α → Prop} {a b c : α}
    (h : TripleMP R a b c) : MonophonicSet R {a,b,c} := by
  intro x hx y hy z hz hxy hxz hyz m f hp hxyz
  obtain ⟨i,j,k,hi,hj,hk⟩ := hxyz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  apply h m f hp
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;> aesop

lemma lower_bound (G : SimpleGraph V) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h : TripleMP G.Adj a b c) :
    3 ≤ mpNumber G := by
  classical
  have hm : {a,b,c} ∈ Finset.univ.filter (MonophonicSet G.Adj) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact mp_triple h
  have hc : ({a,b,c} : Finset V).card = 3 := by simp [hab,hac,hbc]
  simpa only [mpNumber,hc] using (Finset.le_sup (f:=Finset.card) hm)

lemma radius_of_diam (G : SimpleGraph V) (hd : G.diam = 2) :
    ∀ b : V, b=0 ∨ G.Adj 0 b ∨ ∃ c : V, G.Adj 0 c ∧ G.Adj c b := by
  intro b
  have htop := G.ediam_ne_top_of_diam_ne_zero (by omega)
  have hdist := G.dist_le_diam htop (u:=0) (v:=b)
  rw [hd] at hdist
  have he : G.edist 0 b = (G.dist 0 b : ℕ∞) := by
    rw [SimpleGraph.dist]; exact (ENat.natCast_toNat (ne_top_of_le_ne_top htop G.edist_le_ediam)).symm
  have hcases : G.dist 0 b = 0 ∨ G.dist 0 b = 1 ∨ G.dist 0 b = 2 := by omega
  rcases hcases with h | h | h
  · left; have : G.edist 0 b = 0 := by simpa [h] using he
    exact (G.edist_eq_zero_iff.mp this).symm
  · right; left; exact G.edist_eq_one_iff_adj.mp (by simpa [h] using he)
  · right; right
    obtain ⟨c,hc⟩ := (G.edist_eq_two_iff.mp (by simpa [h] using he)).2.2
    exact ⟨c,hc.1,hc.2.symm⟩

theorem order15 (J : Set (ZMod 15))
    (hd : (SimpleGraph.circulantGraph J).diam = 2) :
    3 ≤ mpNumber (SimpleGraph.circulantGraph J) := by
  obtain ⟨s,hs⟩ := represent J
  have hr : RadiusTwoAtZero s := by
    intro b
    rcases radius_of_diam (SimpleGraph.circulantGraph J) hd b with h | h | ⟨c,hc,hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ((hs 0 b).mp h))
    · exact Or.inr (Or.inr ⟨c,(hs 0 c).mp hc,(hs c b).mp hb⟩)
  obtain ⟨a,b,c,hab,hac,hbc,hmp⟩ := obstruction s hr
  apply lower_bound (SimpleGraph.circulantGraph J) a b c hab hac hbc
  intro m f hp
  apply hmp m f
  exact ⟨hp.1,fun i j => (hs (f i) (f j)).symm.trans (hp.2 i j)⟩

-- Source Conjecture 4.5, with actual circulant graphs, diameter and maximum
-- cardinality of a set containing no three vertices of an induced path.
def SourceClaim : Prop := ∀ (n : ℕ) (hn : 11 ≤ n),
  letI : NeZero n := ⟨by omega⟩
  ∃ J : Set (ZMod n),
  (SimpleGraph.circulantGraph J).diam = 2 ∧ mpNumber (SimpleGraph.circulantGraph J) = 2

theorem source_refutation : ¬ SourceClaim := by
  intro h
  obtain ⟨J,hd,hm⟩ := h 15 (by omega)
  have := order15 J hd
  omega
end Circulant350979
