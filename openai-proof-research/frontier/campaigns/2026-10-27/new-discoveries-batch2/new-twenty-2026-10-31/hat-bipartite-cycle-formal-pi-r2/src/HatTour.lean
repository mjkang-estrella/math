import HatCycle
import HatConstr
import Mathlib.Data.Finset.Card

/-!
# HatTour: the alternating tour is a genuine Hamilton circuit

Milestone 2 of the MathDB 325100 endpoint (continuation of HatCycle and
HatConstr).  For every `s >= 2`, any injective labelling `x : Fin s ->
Fin (2*s)` of the odd labels with `x 0 = 1` and `x (s-1) = 2*s-1`, and any
map `t : Fin (s-1) -> Fin (2*s)` into the positive even labels, the
alternating edge set `{x j -- t j} u {t j -- x (j+1)} u {0 -- x 0,
0 -- x (s-1)}` carries every label on exactly two edges and is
walk-connected; it is therefore an actual `HamCirc s`: a literal connected
2-regular spanning subgraph of the source hat graph, built from the
baseline edge constructors `tourAB`/`tourBA` and genuine z-edges.

Nothing about the tour is assumed: the covering of the odd resp. positive
even labels used by the degree count is *derived* (an injection of `Fin s`
into the `s` odd labels is onto; likewise `t` against the `s-1` positive
even labels), by finite-image cardinality, not by any rank or dimension
computation.  Injectivity of both `x` and `t` is a genuine hypothesis: a
repeated `t`-value would produce a vertex of degree 3, so the tour theorem
fails without it.

Later milestones (rectangles from two tours, kernel clearing, z-cancellation,
final equality) are separate modules.
-/

theorem hatCan_fst (s : Nat) (a b : Fin (2 * s)) :
    (hatCan s a b).1.val = min a.val b.val := rfl

theorem hatCan_snd (s : Nat) (a b : Fin (2 * s)) :
    (hatCan s a b).2.val = max a.val b.val := rfl

theorem castLE_val {m n : Nat} {h : m ≤ n} (j : Fin m) :
    (Fin.castLE h j).val = j.val := rfl

/-- The `i`-th odd label `2i+1`. -/
def oddV (s : Nat) (i : Fin s) : Fin (2 * s) := ⟨2 * i.val + 1, by omega⟩

/-- The `k`-th positive even label `2k+2`. -/
def evenV (s : Nat) (k : Fin (s - 1)) : Fin (2 * s) := ⟨2 * k.val + 2, by omega⟩

theorem oddV_val (s : Nat) (i : Fin s) : (oddV s i).val = 2 * i.val + 1 := rfl

theorem evenV_val (s : Nat) (k : Fin (s - 1)) : (evenV s k).val = 2 * k.val + 2 := rfl

theorem oddV_inj (s : Nat) : Function.Injective (oddV s) := by
  intro i j h
  have hv : (oddV s i).val = (oddV s j).val := by rw [h]
  rw [oddV_val, oddV_val] at hv
  exact Fin.val_injective hv

theorem evenV_inj (s : Nat) : Function.Injective (evenV s) := by
  intro k l h
  have hv : (evenV s k).val = (evenV s l).val := by rw [h]
  rw [evenV_val, evenV_val] at hv
  exact Fin.val_injective hv

theorem oddV_odd (s : Nat) (i : Fin s) : (oddV s i).val % 2 = 1 := by
  rw [oddV_val]; omega

theorem evenV_even (s : Nat) (k : Fin (s - 1)) : (evenV s k).val % 2 = 0 := by
  rw [evenV_val]; omega

theorem evenV_nz (s : Nat) (k : Fin (s - 1)) : (evenV s k).val ≠ 0 := by
  rw [evenV_val]; omega

theorem ne_odd_even {s : Nat} {v w : Fin (2 * s)} (hv : v.val % 2 = 1)
    (hw : w.val % 2 = 0) : v ≠ w := by
  intro h
  have hval : v.val = w.val := by rw [h]
  omega

/-- The odd labels are exactly the values of `oddV`. -/
theorem oddImage (s : Nat) :
    Finset.univ.filter (fun v : Fin (2 * s) => v.val % 2 = 1)
      = Finset.image (oddV s) Finset.univ := by
  ext v
  rw [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    have hvlt : v.val < 2 * s := v.isLt
    refine ⟨⟨(v.val - 1) / 2, by omega⟩, ?_⟩
    exact Fin.val_injective (by show 2 * ((v.val - 1) / 2) + 1 = v.val; omega)
  · intro hi
    obtain ⟨i, hi⟩ := hi
    have hv : (oddV s i).val = v.val := by rw [hi]
    rw [oddV_val] at hv
    omega

/-- The positive even labels are exactly the values of `evenV`. -/
theorem evenImage (s : Nat) :
    Finset.univ.filter (fun v : Fin (2 * s) => v.val % 2 = 0 ∧ v.val ≠ 0)
      = Finset.image (evenV s) Finset.univ := by
  ext v
  rw [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨hp, hz⟩ := h
    have hvlt : v.val < 2 * s := v.isLt
    refine ⟨⟨(v.val - 2) / 2, by omega⟩, ?_⟩
    exact Fin.val_injective (by show 2 * ((v.val - 2) / 2) + 2 = v.val; omega)
  · intro hi
    obtain ⟨k, hk⟩ := hi
    have hv : (evenV s k).val = v.val := by rw [hk]
    rw [evenV_val] at hv
    omega

theorem card_odd (s : Nat) :
    (Finset.univ.filter (fun v : Fin (2 * s) => v.val % 2 = 1)).card = s := by
  rw [oddImage, Finset.card_image_of_injective Finset.univ (oddV_inj s), Finset.card_fin]

theorem card_even (s : Nat) :
    (Finset.univ.filter (fun v : Fin (2 * s) => v.val % 2 = 0 ∧ v.val ≠ 0)).card = s - 1 := by
  rw [evenImage, Finset.card_image_of_injective Finset.univ (evenV_inj s), Finset.card_fin]

/-- The last index of `Fin s` (well formed for `s >= 1`). -/
def hatLast (s : Nat) (_hs : 2 <= s) : Fin s := ⟨s - 1, by omega⟩

section Tour

variable {s : Nat} (hs : 2 ≤ s) (x : Fin s → Fin (2 * s))
  (hxi : Function.Injective x) (hxo : ∀ i, (x i).val % 2 = 1)
  (t : Fin (s - 1) → Fin (2 * s)) (hti : Function.Injective t)
  (hto : ∀ j, (t j).val % 2 = 0) (htz : ∀ j, (t j).val ≠ 0)
  (h0 : (x 0).val = 1) (hl : (x (hatLast s hs)).val = 2 * s - 1)

/-- The last index of `Fin s`. -/
theorem xcast (j : Fin (s - 1)) :
    x (Fin.castLE (show s - 1 ≤ s by omega) j) = x j :=
  congrArg x (Fin.ext (castLE_val j))

/-- The two z-edges of the tour: `0 -- x 0` and `0 -- x (s-1)`. -/
def zEA : HEdge s :=
  ⟨hatCan s 0 (x 0), by
    unfold hatEdgeSet
    rw [Finset.mem_filter, hatCan_fst, hatCan_snd]
    exact ⟨Finset.mem_univ _, ⟨by omega, Or.inr ⟨by omega, Or.inl (by omega)⟩⟩⟩⟩

def zEB : HEdge s :=
  ⟨hatCan s 0 (x (hatLast s hs)), by
    unfold hatEdgeSet
    rw [Finset.mem_filter, hatCan_fst, hatCan_snd]
    exact ⟨Finset.mem_univ _, ⟨by omega, Or.inr ⟨by omega, Or.inr (by omega)⟩⟩⟩⟩

/-- The A-B tour edge `x j -- t j`. -/
def tourA (j : Fin (s - 1)) : HEdge s := tourAB s x t hxo hto htz j

/-- The B-A tour edge `t j -- x (j+1)`. -/
def tourB (j : Fin (s - 1)) : HEdge s := tourBA s x t hxo hto htz j

/-- The tour edge set. -/
def tourE : Finset (HEdge s) :=
  Finset.univ.image (fun j : Fin (s - 1) => tourA j) ∪
    Finset.univ.image (fun j : Fin (s - 1) => tourB j) ∪ {zEA, zEB}

theorem mem_tourE (e : HEdge s) :
    e ∈ tourE ↔ (∃ j, e = tourA j) ∨ (∃ j, e = tourB j) ∨ e = zEA ∨ e = zEB := by
  simp only [tourE, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem tourA_mem (j : Fin (s - 1)) : tourA j ∈ tourE :=
  (mem_tourE (tourA j)).2 (Or.inl ⟨j, rfl⟩)

theorem tourB_mem (j : Fin (s - 1)) : tourB j ∈ tourE :=
  (mem_tourE (tourB j)).2 (Or.inr (Or.inl ⟨j, rfl⟩))

theorem zEA_mem : zEA ∈ tourE := (mem_tourE zEA).2 (Or.inr (Or.inr (Or.inl rfl)))

theorem zEB_mem : zEB ∈ tourE := (mem_tourE zEB).2 (Or.inr (Or.inr (Or.inr rfl)))

/-- Membership of a tour-A edge in the tour, phrased for the degree count. -/
theorem tourA_pair (j : Fin (s - 1)) :
    (tourA j).1 = (x j, t j) ∨ (tourA j).1 = (t j, x j) := by
  have hU : (tourA j).1 = hatCan s (x (Fin.castLE (show s - 1 ≤ s by omega) j)) (t j) := rfl
  rw [hU, xcast]
  exact hatCan_or (x j) (t j)

theorem tourB_pair (j : Fin (s - 1)) :
    (tourB j).1 = (t j, x (tourSucc s j)) ∨ (tourB j).1 = (x (tourSucc s j), t j) := by
  have hU : (tourB j).1 = hatCan s (t j) (x (tourSucc s j)) := rfl
  rw [hU]
  exact hatCan_or (t j) (x (tourSucc s j))

/-- Incidence at a vertex is membership in the endpoint pair. -/
theorem incid_pair {s : Nat} {v a b : Fin (2 * s)} (h : hatCan s a b ∈ hatEdgeSet s) :
    IncidP s v (⟨hatCan s a b, h⟩ : HEdge s) ↔ v = a ∨ v = b := by
  constructor
  · rintro (he | he)
    · have hv : (hatCan s a b).1.val = v.val := by rw [he]
      rw [hatCan_fst] at hv
      rcases Nat.lt_or_ge a.val b.val with hlt | hge
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    · have hv : (hatCan s a b).2.val = v.val := by rw [he]
      rw [hatCan_snd] at hv
      rcases Nat.lt_or_ge a.val b.val with hlt | hge
      · exact Or.inr (Fin.ext (by omega))
      · exact Or.inl (Fin.ext (by omega))
  · rintro (h | h)
    · rcases Nat.lt_or_ge a.val b.val with hlt | hge
      · refine Or.inl (Fin.ext ?_)
        have := congrArg (fun w : Fin (2 * s) => w.val) h
        show min a.val b.val = v.val
        omega
      · refine Or.inr (Fin.ext ?_)
        have := congrArg (fun w : Fin (2 * s) => w.val) h
        show max a.val b.val = v.val
        omega
    · rcases Nat.lt_or_ge a.val b.val with hlt | hge
      · refine Or.inr (Fin.ext ?_)
        have := congrArg (fun w : Fin (2 * s) => w.val) h
        show max a.val b.val = v.val
        omega
      · refine Or.inl (Fin.ext ?_)
        have := congrAgr (fun w : Fin (2 * s) => w.val) h
        show min a.val b.val = v.val
        omega

theorem incidA (j : Fin (s - 1)) (v : Fin (2 * s)) :
    IncidP s v (tourA j) ↔ v = x (Fin.castLE (show s - 1 ≤ s by omega) j) ∨ v = t j :=
  incid_pair (tourA j).2

theorem incidA' (j : Fin (s - 1)) (v : Fin (2 * s)) :
    IncidP s v (tourA j) ↔ v = x j ∨ v = t j := by
  rw [incidA j v, xcast j]
  exact Iff.rfl

theorem incidB (j : Fin (s - 1)) (v : Fin (2 * s)) :
    IncidP s v (tourB j) ↔ v = t j ∨ v = x (tourSucc s j) :=
  incid_pair (tourB j).2

theorem incidEA (v : Fin (2 * s)) : IncidP s v zEA ↔ v = 0 ∨ v = x 0 :=
  incid_pair zEA.2

theorem incidEB (v : Fin (2 * s)) :
    IncidP s v zEB ↔ v = 0 ∨ v = x (hatLast s hs) :=
  incid_pair zEB.2

theorem zNE : zEA ≠ zEB := by
  intro h
  have h1 : zEA.1.2.val = 1 := by
    show (hatCan s 0 (x 0)).2.val = 1
    rw [hatCan_snd]; omega
  have h2 : zEB.1.2.val = 2 * s - 1 := by
    show (hatCan s 0 (x (hatLast s hs))).2.val = 2 * s - 1
    rw [hatCan_snd]; omega
  have h3 : zEA.1.2 = zEB.1.2 := by rw [h]
  have h4 : zEA.1.2.val = zEB.1.2.val := congrArg (fun w : Fin (2 * s) => w.val) h3
  rw [h1, h2] at h4
  omega

/-- Every odd label is a value of `x`. -/
theorem x_surj (v : Fin (2 * s)) (hv : v.val % 2 = 1) : ∃ i, x i = v := by
  have hsub : Finset.image x Finset.univ
      ⊆ Finset.univ.filter (fun w : Fin (2 * s) => w.val % 2 = 1) := by
    intro w hw
    rw [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter] at hw ⊢
    obtain ⟨i, -, rfl⟩ := hw
    exact hxo i
  have himg : Finset.image x Finset.univ
      = Finset.univ.filter (fun w : Fin (2 * s) => w.val % 2 = 1) :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [card_odd, Finset.card_image_of_injective Finset.univ hxi, Finset.card_fin])
  have hvm : v ∈ Finset.univ.filter (fun w : Fin (2 * s) => w.val % 2 = 1) := by
    rw [Finset.mem_filter, Finset.mem_univ, true_and]; exact hv
  rw [← himg] at hvm
  rw [Finset.mem_image] at hvm
  obtain ⟨i, -, h⟩ := hvm
  exact ⟨i, h⟩

/-- Every positive even label is a value of `t`. -/
theorem t_surj (v : Fin (2 * s)) (hv0 : v.val ≠ 0) (hv : v.val % 2 = 0) :
    ∃ j, t j = v := by
  have hsub : Finset.image t Finset.univ
      ⊆ Finset.univ.filter (fun w : Fin (2 * s) => w.val % 2 = 0 ∧ w.val ≠ 0) := by
    intro w hw
    rw [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter] at hw ⊢
    obtain ⟨j, -, rfl⟩ := hw
    exact ⟨hto j, htz j⟩
  have himg : Finset.image t Finset.univ
      = Finset.univ.filter (fun w : Fin (2 * s) => w.val % 2 = 0 ∧ w.val ≠ 0) :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [card_even, Finset.card_image_of_injective Finset.univ hti, Finset.card_fin])
  have hvm : v ∈ Finset.univ.filter (fun w : Fin (2 * s) => w.val % 2 = 0 ∧ w.val ≠ 0) := by
    rw [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hv, hv0⟩
  rw [← himg] at hvm
  rw [Finset.mem_image] at hvm
  obtain ⟨j, -, h⟩ := hvm
  exact ⟨j, h⟩

end Tour
