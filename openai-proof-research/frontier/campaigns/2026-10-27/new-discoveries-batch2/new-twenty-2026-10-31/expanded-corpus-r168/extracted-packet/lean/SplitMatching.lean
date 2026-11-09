import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option maxHeartbeats 0
namespace SplitMatching381751
theorem local_arithmetic (a b c d e f g h i j k l : ℕ)
 (h0 : a+f+i ≤ 1) (h1 : a+e+j ≤ 1) (h2 : b+e+i ≤ 1)
 (h3 : b+f+k ≤ 1) (h4 : c+h+j ≤ 1) (h5 : c+g+l ≤ 1)
 (h6 : d+g+k ≤ 1) (h7 : d+h+l ≤ 1)
 (ha : a+b+c+d ≤ 1) (hb : e+f+g+h ≤ 3) (hc : i+j+k+l ≤ 3) :
 a+b+c+d+e+f+g+h+i+j+k+l ≤ 3 := by omega

abbrev LE := Fin 12
abbrev LV := Fin 8
abbrev E := Fin 2 × LE
abbrev V := Fin 2 × LV
def left (e : LE) : LV := ![0,2,4,6,1,0,5,4,0,1,3,5] e
def right (e : LE) : LV := ![1,3,5,7,2,3,6,7,2,4,6,7] e
def colour (e : LE) : Fin 3 := ⟨e.val / 4, by omega⟩
def w (b : Bool) : ℕ := if b then 1 else 0
def degree (s : LE → Bool) (v : LV) : ℕ :=
 ∑ e : LE, if left e = v ∨ right e = v then w (s e) else 0
def lc (s : LE → Bool) (c : Fin 3) : ℕ :=
 ∑ e : LE, if colour e = c then w (s e) else 0
def matching (s : E → Bool) : Prop := ∀ b v, degree (fun e => s (b,e)) v ≤ 1
def count (s : E → Bool) (c : Fin 3) : ℕ := lc (fun e => s (0,e)) c + lc (fun e => s (1,e)) c
-- Literal simple incidence graph; no loops or parallel edges.
theorem simple_edges : (∀ e : LE, left e ≠ right e) ∧
 (∀ e f : LE, (left e = left f ∧ right e = right f) ∨
 (left e = right f ∧ right e = left f) → e = f) := by decide
-- Every colour is a perfect matching on the eight local vertices.
theorem perfect_colours : ∀ c : Fin 3, ∀ v : LV,
 (Finset.univ.filter (fun e : LE => colour e = c ∧ (left e = v ∨ right e = v))).card = 1 := by decide
-- A matching in the graph is precisely a selection with incident degree at most one.
theorem local_restriction (s : LE → Bool) (hm : ∀ v, degree s v ≤ 1)
 (h0 : lc s 0 ≤ 1) (h1 : lc s 1 ≤ 3) (h2 : lc s 2 ≤ 3) :
 lc s 0 + lc s 1 + lc s 2 ≤ 3 := by
 have H0 := hm 0; have H1 := hm 1; have H2 := hm 2; have H3 := hm 3
 have H4 := hm 4; have H5 := hm 5; have H6 := hm 6; have H7 := hm 7
 norm_num [degree, Fin.sum_univ_succ, left, right] at H0 H1 H2 H3 H4 H5 H6 H7
 norm_num [lc, colour, Fin.sum_univ_succ] at h0 h1 h2 ⊢
 have hh := local_arithmetic (w (s 0)) (w (s 1)) (w (s 2)) (w (s 3))
  (w (s 4)) (w (s 5)) (w (s 6)) (w (s 7)) (w (s 8)) (w (s 9)) (w (s 10)) (w (s 11))
  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
 omega
theorem no_split (s : E → Bool) (hm : matching s) :
 ¬ (count s 0 = 1 ∧ count s 1 = 3 ∧ count s 2 = 3) := by
 intro ⟨h0,h1,h2⟩
 have b0 := local_restriction (fun e => s (0,e)) (hm 0)
 have b1 := local_restriction (fun e => s (1,e)) (hm 1)
 simp only [count] at h0 h1 h2
 have a0 : lc (fun e => s (0,e)) 0 ≤ 1 := by omega
 have a1 : lc (fun e => s (0,e)) 1 ≤ 3 := by omega
 have a2 : lc (fun e => s (0,e)) 2 ≤ 3 := by omega
 have c0 : lc (fun e => s (1,e)) 0 ≤ 1 := by omega
 have c1 : lc (fun e => s (1,e)) 1 ≤ 3 := by omega
 have c2 : lc (fun e => s (1,e)) 2 ≤ 3 := by omega
 have := b0 a0 a1 a2
 have := b1 c0 c1 c2
 omega
def graph : SimpleGraph V where
 Adj x y := x.1 = y.1 ∧ ∃ e : LE,
  (left e = x.2 ∧ right e = y.2) ∨ (right e = x.2 ∧ left e = y.2)
 symm := ⟨by
  rintro x y ⟨hb,e,he⟩
  refine ⟨hb.symm,e,?_⟩
  rcases he with ⟨hl,hr⟩ | ⟨hr,hl⟩
  · exact Or.inr ⟨hr,hl⟩
  · exact Or.inl ⟨hl,hr⟩⟩
 loopless := ⟨by
  rintro x ⟨_,e,he⟩
  rcases he with ⟨hl,hr⟩ | ⟨hr,hl⟩
  · exact simple_edges.1 e (hl.trans hr.symm)
  · exact simple_edges.1 e (hl.trans hr.symm)⟩
instance : DecidableRel graph.Adj := by
 intro x y
 change Decidable (x.1 = y.1 ∧ ∃ e : LE,
  (left e = x.2 ∧ right e = y.2) ∨ (right e = x.2 ∧ left e = y.2))
 infer_instance
-- Five distinct vertices in one connected component rule out a K4 component.
def five (i : Fin 5) : V := (0, ⟨i.val, by omega⟩)
theorem five_injective : Function.Injective five := by
 intro i j h
 have : i.val = j.val := congrArg (fun v : V => v.2.val) h
 exact Fin.ext this
theorem five_reachable (i : Fin 5) : graph.Reachable (0,0) (five i) := by
 have h01 : graph.Adj (0,0) (0,1) := by decide
 have h02 : graph.Adj (0,0) (0,2) := by decide
 have h03 : graph.Adj (0,0) (0,3) := by decide
 have h14 : graph.Adj (0,1) (0,4) := by decide
 fin_cases i
 · exact SimpleGraph.Reachable.rfl
 · exact h01.reachable
 · exact h02.reachable
 · exact h03.reachable
 · exact h01.reachable.trans h14.reachable
theorem component_at_least_five :
 5 ≤ Nat.card {v : V // graph.Reachable (0,0) v} := by
 let f : Fin 5 → {v : V // graph.Reachable (0,0) v} := fun i => ⟨five i, five_reachable i⟩
 have hf : Function.Injective f := by
  intro i j h
  exact five_injective (congrArg Subtype.val h)
 have := Nat.card_le_card_of_injective f hf
 simpa using this
-- Global edge endpoints give the literal partition into three perfect matchings.
def L (e : E) : V := (e.1,left e.2)
def R (e : E) : V := (e.1,right e.2)
theorem global_simple : (∀ e : E, L e ≠ R e) ∧
 (∀ e f : E, (L e = L f ∧ R e = R f) ∨ (L e = R f ∧ R e = L f) → e = f) := by decide
theorem global_perfect : ∀ c : Fin 3, ∀ v : V,
 (Finset.univ.filter (fun e : E => colour e.2 = c ∧ (L e = v ∨ R e = v))).card = 1 := by decide
-- Every graph edge has exactly one identifier. Thus selection functions describe all
-- arbitrary edge subsets, and degree <= 1 is the usual matching condition.
theorem graph_edge_iff (x y : V) : graph.Adj x y ↔
 ∃ e : E, (L e = x ∧ R e = y) ∨ (R e = x ∧ L e = y) := by
 constructor
 · rintro ⟨hb,e,he⟩
   refine ⟨(x.1,e),?_⟩
   rcases he with ⟨hl,hr⟩ | ⟨hr,hl⟩
   · exact Or.inl ⟨Prod.ext rfl hl,Prod.ext hb hr⟩
   · exact Or.inr ⟨Prod.ext rfl hr,Prod.ext hb hl⟩
 · rintro ⟨e,⟨hl,hr⟩ | ⟨hr,hl⟩⟩
   · have hx : e.1 = x.1 := congrArg (fun v : V => v.1) hl
     have hy : e.1 = y.1 := congrArg (fun v : V => v.1) hr
     exact ⟨hx.symm.trans hy,e.2,Or.inl ⟨congrArg Prod.snd hl,congrArg Prod.snd hr⟩⟩
   · have hx : e.1 = x.1 := congrArg (fun v : V => v.1) hr
     have hy : e.1 = y.1 := congrArg (fun v : V => v.1) hl
     exact ⟨hx.symm.trans hy,e.2,Or.inr ⟨congrArg Prod.snd hr,congrArg Prod.snd hl⟩⟩
theorem counterexample : Fintype.card V = 16 ∧
 (∀ c : Fin 3, ∀ v : V, (Finset.univ.filter (fun e : E =>
  colour e.2 = c ∧ (L e = v ∨ R e = v))).card = 1) ∧
 5 ≤ Nat.card {v : V // graph.Reachable (0,0) v} ∧
 ¬ ∃ s : E → Bool, matching s ∧ count s 0 = 1 ∧ count s 1 = 3 ∧ count s 2 = 3 := by
 refine ⟨by decide, global_perfect, component_at_least_five, ?_⟩
 rintro ⟨s,hm,h0,h1,h2⟩
 exact no_split s hm ⟨h0,h1,h2⟩

theorem degree_card (s : LE → Bool) (v : LV) : degree s v =
 (Finset.univ.filter (fun e : LE => s e = true ∧ (left e = v ∨ right e = v))).card := by
 rw [Finset.card_eq_sum_ones, Finset.sum_filter]
 unfold degree
 apply Finset.sum_congr rfl
 intro e _
 cases hs : s e <;> by_cases he : left e = v ∨ right e = v <;> simp [w,he]
theorem lc_card (s : LE → Bool) (c : Fin 3) : lc s c =
 (Finset.univ.filter (fun e : LE => s e = true ∧ colour e = c)).card := by
 rw [Finset.card_eq_sum_ones, Finset.sum_filter]
 unfold lc
 apply Finset.sum_congr rfl
 intro e _
 cases hs : s e <;> by_cases he : colour e = c <;> simp [w,he]
theorem count_card (s : E → Bool) (c : Fin 3) : count s c =
 (Finset.univ.filter (fun e : E => s e = true ∧ colour e.2 = c)).card := by
 rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
 rw [Fin.sum_univ_two]
 unfold count lc
 congr 1 <;> apply Finset.sum_congr rfl <;> intro e _
 · cases hs : s (0,e) <;> by_cases he : colour e = c <;> simp [w,he] <;> assumption
 · cases hs : s (1,e) <;> by_cases he : colour e = c <;> simp [w,he] <;> assumption

theorem literal_counterexample : Fintype.card V = 16 ∧
 (∀ e : E, L e ≠ R e) ∧
 (∀ e f : E, (L e = L f ∧ R e = R f) ∨ (L e = R f ∧ R e = L f) → e = f) ∧
 (∀ c : Fin 3, ∀ v : V, (Finset.univ.filter (fun e : E =>
  colour e.2 = c ∧ (L e = v ∨ R e = v))).card = 1) ∧
 5 ≤ Nat.card {v : V // graph.Reachable (0,0) v} ∧
 ¬ ∃ s : E → Bool,
 (∀ b : Fin 2, ∀ v : LV, (Finset.univ.filter (fun e : LE =>
  s (b,e) = true ∧ (left e = v ∨ right e = v))).card ≤ 1) ∧
 (Finset.univ.filter (fun e : E => s e = true ∧ colour e.2 = 0)).card = 1 ∧
 (Finset.univ.filter (fun e : E => s e = true ∧ colour e.2 = 1)).card = 3 ∧
 (Finset.univ.filter (fun e : E => s e = true ∧ colour e.2 = 2)).card = 3 := by
 refine ⟨by decide,global_simple.1,global_simple.2,global_perfect,component_at_least_five,?_⟩
 rintro ⟨s,hm,h0,h1,h2⟩
 have hm2 : matching s := by
  intro b v
  rw [degree_card]
  exact hm b v
 exact no_split s hm2 ⟨(count_card s 0).trans h0,(count_card s 1).trans h1,(count_card s 2).trans h2⟩
#print axioms literal_counterexample
end SplitMatching381751
