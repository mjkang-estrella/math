# Lean source appendix

Modules are listed in import order.

## ThetaCore.lean

```lean
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases

namespace Theta359778

open SimpleGraph

/-- Three paths of length `k + 2` have two common terminals and `k + 1`
internal vertices per path. -/
abbrev Vertex (k : ℕ) := Option (Option (Fin 3 × Fin (k + 1)))

abbrev Index (k : ℕ) := Fin 3 × Fin (k + 2)

def start (k : ℕ) : Vertex k := none

def finish (k : ℕ) : Vertex k := some none

def vertex (k : ℕ) (p : Fin 3) (i : ℕ) : Vertex k :=
  if i = 0 then start k
  else if hi : i ≤ k + 1 then some (some (p, ⟨i - 1, by omega⟩))
  else finish k

@[simp] theorem vertex_zero (p : Fin 3) : vertex k p 0 = start k := by
  simp [vertex]

@[simp] theorem vertex_finish (p : Fin 3) : vertex k p (k + 2) = finish k := by
  simp [vertex, show ¬ k + 2 ≤ k + 1 by omega]

@[simp] theorem vertex_inside (p : Fin 3) (i : Fin (k + 1)) :
    vertex k p (i.val + 1) = some (some (p, i)) := by
  simp [vertex, show i.val + 1 ≤ k + 1 by omega]

def level (k : ℕ) : Vertex k → ℕ
  | none => 0
  | some none => k + 2
  | some (some (_, i)) => i.val + 1

theorem level_vertex (p : Fin 3) {i : ℕ} (hi : i ≤ k + 2) :
    level k (vertex k p i) = i := by
  unfold vertex
  split
  · subst i
    rfl
  split
  · change i - 1 + 1 = i
    omega
  · change k + 2 = i
    omega

theorem vertex_path_eq {p q : Fin 3} {i : ℕ} (h0 : 0 < i) (hi : i ≤ k + 1)
    (he : vertex k p i = vertex k q i) : p = q := by
  simpa [vertex, Nat.ne_of_gt h0, hi] using he

def edge (k : ℕ) (e : Index k) : Sym2 (Vertex k) :=
  s(vertex k e.1 e.2.val, vertex k e.1 (e.2.val + 1))

theorem edge_not_diag (e : Index k) : ¬ (edge k e).IsDiag := by
  rw [edge, Sym2.mk_isDiag_iff]
  intro h
  have H := congrArg (level k) h
  rw [level_vertex _ (by omega), level_vertex _ (by omega)] at H
  omega

theorem edge_injective (k : ℕ) : Function.Injective (edge k) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  change s(vertex k p i.val, vertex k p (i.val + 1)) =
    s(vertex k q j.val, vertex k q (j.val + 1)) at h
  have h := (@Sym2.mk_eq_mk_iff _ (vertex k p i.val, vertex k p (i.val + 1))
    (vertex k q j.val, vertex k q (j.val + 1))).mp h
  rcases h with h | h
  · have hl := congrArg Prod.fst h
    have hr := congrArg Prod.snd h
    change vertex k p i.val = vertex k q j.val at hl
    change vertex k p (i.val + 1) = vertex k q (j.val + 1) at hr
    have he := congrArg (level k) hl
    rw [level_vertex _ (by omega), level_vertex _ (by omega)] at he
    have hij : i = j := Fin.ext he
    subst j
    have hpq : p = q := by
      by_cases hi : i.val = 0
      · exact vertex_path_eq (by omega) (by omega) hr
      · exact vertex_path_eq (by omega) (by omega) hl
    subst q
    rfl
  · have hl := congrArg Prod.fst h
    have hr := congrArg Prod.snd h
    change vertex k p i.val = vertex k q (j.val + 1) at hl
    change vertex k p (i.val + 1) = vertex k q j.val at hr
    have h₁ := congrArg (level k) hl
    have h₂ := congrArg (level k) hr
    rw [level_vertex _ (by omega), level_vertex _ (by omega)] at h₁ h₂
    omega

open Finset in
def core (k : ℕ) : Finset (Sym2 (Vertex k)) :=
  univ.map ⟨edge k, edge_injective k⟩

@[simp] theorem edge_mem_core (e : Index k) : edge k e ∈ core k :=
  Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩

theorem core_subset_top (k : ℕ) :
    core k ⊆ (⊤ : SimpleGraph (Vertex k)).edgeFinset := by
  intro e he
  obtain ⟨idx, -, rfl⟩ := Finset.mem_map.mp he
  exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_top ▸ edge_not_diag idx)

@[simp] theorem card_vertex (k : ℕ) : Fintype.card (Vertex k) = 3 * (k + 2) - 1 := by
  simp [Vertex, Fintype.card_option, Fintype.card_prod]
  omega

@[simp] theorem card_core (k : ℕ) : (core k).card = 3 * (k + 2) := by
  simp [core, Index, Fintype.card_prod]

/-- Number of Mathlib connected components of a finite graph. -/
noncomputable def compCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact Fintype.card G.ConnectedComponent

theorem compCount_le_of_le {V : Type} [Fintype V] {G H : SimpleGraph V} (h : G ≤ H) :
    compCount H ≤ compCount G := by
  classical
  simpa only [compCount, Nat.card_eq_fintype_card] using
    ConnectedComponent.card_le_card_of_le h

end Theta359778
```

## ThetaReach.lean

```lean
import ThetaCore

namespace Theta359778

open SimpleGraph Finset

/-- The final index is a sentinel meaning the path has no omitted edge. -/
def uncut (k : ℕ) : Fin (k + 3) := Fin.last (k + 2)

abbrev Choices (k : ℕ) := Fin 3 → Fin (k + 3)

/-- At least one path has no omitted edge. -/
abbrev Pattern (k : ℕ) := {a : Choices k // ∃ p, a p = uncut k}

def common (a b : Choices k) : SimpleGraph (Vertex k) :=
  fromEdgeSet {e | ∃ i : Index k, edge k i = e ∧
    i.2.val ≠ (a i.1).val ∧ i.2.val ≠ (b i.1).val}

theorem reachable_interval (a b : Choices k) (p : Fin 3) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k + 2)
    (keep : ∀ l : ℕ, i ≤ l → l < j → l ≠ (a p).val ∧ l ≠ (b p).val) :
    (common a b).Reachable (vertex k p i) (vertex k p j) := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact Reachable.rfl
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i
      exact Reachable.rfl
    have hj' : j < k + 2 := by omega
    have hi' : i ≤ j := by omega
    have H := ih hi' (by omega) (fun l hil hlj ↦ keep l hil (by omega))
    let idx : Index k := (p, ⟨j, hj'⟩)
    have hadj : (common a b).Adj (vertex k p j) (vertex k p (j + 1)) :=
      (fromEdgeSet_adj _).mpr ⟨⟨idx, rfl, keep j hi' (by omega)⟩,
        fun h ↦ edge_not_diag idx (Sym2.mk_isDiag_iff.mpr h)⟩
    exact H.trans hadj.reachable

def twiceCut (a b : Choices k) (p : Fin 3) : Prop :=
  (a p).val < k + 2 ∧ (b p).val < k + 2 ∧ a p ≠ b p

noncomputable def doublePaths (a b : Choices k) : Finset (Fin 3) := by
  classical
  exact univ.filter (twiceCut a b)

@[simp] theorem mem_doublePaths {a b : Choices k} {p : Fin 3} :
    p ∈ doublePaths a b ↔ twiceCut a b p := by
  classical
  simp [doublePaths]

def middleRep (a b : Choices k) (p : Fin 3) : Vertex k :=
  vertex k p (min (a p).val (b p).val + 1)

theorem reachable_representative (a b : Choices k) (v : Vertex k) :
    (common a b).Reachable v (start k) ∨
    (common a b).Reachable v (finish k) ∨
    ∃ p ∈ doublePaths a b, (common a b).Reachable v (middleRep a b p) := by
  rcases v with _ | (_ | ⟨p, x⟩)
  · exact Or.inl Reachable.rfl
  · exact Or.inr (Or.inl Reachable.rfl)
  rw [← vertex_inside]
  let i := x.val + 1
  change (common a b).Reachable (vertex k p i) (start k) ∨
    (common a b).Reachable (vertex k p i) (finish k) ∨ _
  have hi : i ≤ k + 1 := by dsimp [i]; omega
  have ha : (a p).val ≤ k + 2 := by omega
  have hb : (b p).val ≤ k + 2 := by omega
  by_cases head : i ≤ (a p).val ∧ i ≤ (b p).val
  · left
    rw [← vertex_zero (k := k) p]
    exact (reachable_interval a b p (by omega) (by omega)
      (fun l _ hl ↦ ⟨by omega, by omega⟩)).symm
  by_cases tail : ((a p).val = k + 2 ∨ (a p).val < i) ∧
      ((b p).val = k + 2 ∨ (b p).val < i)
  · right; left
    rw [← vertex_finish (k := k) p]
    exact reachable_interval a b p (by omega) (by omega)
      (fun l hl hj ↦ ⟨by omega, by omega⟩)
  right; right
  have hmin : min (a p).val (b p).val < i := by omega
  have hmax : i ≤ max (a p).val (b p).val := by omega
  have hne : (a p).val ≠ (b p).val := by omega
  refine ⟨p, mem_doublePaths.mpr ⟨by omega, by omega,
    fun h ↦ hne (congrArg Fin.val h)⟩, ?_⟩
  exact (reachable_interval a b p (by omega) (by omega)
    (fun l hl hj ↦ ⟨by omega, by omega⟩)).symm

theorem reachable_terminals (a b : Choices k) (p : Fin 3)
    (ha : a p = uncut k) (hb : b p = uncut k) :
    (common a b).Reachable (start k) (finish k) := by
  rw [← vertex_zero (k := k) p, ← vertex_finish (k := k) p]
  apply reachable_interval a b p (by omega) (by omega)
  intro l _ hl
  simpa [ha, hb, uncut] using Nat.ne_of_lt hl

theorem card_doublePaths_le_two (a b : Pattern k) :
    (doublePaths a.val b.val).card ≤ 2 := by
  classical
  obtain ⟨p, hp⟩ := a.property
  have hn : p ∉ doublePaths a.val b.val := by
    simp [twiceCut, hp, uncut]
  have H : doublePaths a.val b.val ⊆ univ.erase p :=
    fun q hq ↦ mem_erase.mpr ⟨fun he ↦ hn (he ▸ hq), mem_univ _⟩
  simpa [card_erase_of_mem (mem_univ p)] using card_le_card H

theorem card_doublePaths_le_one (a b : Pattern k)
    (noFull : ¬ ∃ p, a.val p = uncut k ∧ b.val p = uncut k) :
    (doublePaths a.val b.val).card ≤ 1 := by
  classical
  rw [card_le_one]
  intro p hp q hq
  by_contra hn
  obtain ⟨r, hr⟩ := a.property
  obtain ⟨s, hs⟩ := b.property
  have hpd := mem_doublePaths.mp hp
  have hqd := mem_doublePaths.mp hq
  have hpa : p ≠ r := by
    rintro rfl
    simp [twiceCut, hr, uncut] at hpd
  have hqa : q ≠ r := by
    rintro rfl
    simp [twiceCut, hr, uncut] at hqd
  have hpb : p ≠ s := by
    rintro rfl
    simp [twiceCut, hs, uncut] at hpd
  have hqb : q ≠ s := by
    rintro rfl
    simp [twiceCut, hs, uncut] at hqd
  have h : r = s := by
    apply Fin.ext
    simp only [← Fin.val_ne_iff] at hn hpa hqa hpb hqb
    omega
  exact noFull ⟨r, hr, h ▸ hs⟩

theorem compCount_le_of_representatives {V : Type} [Fintype V] {G : SimpleGraph V}
    (R : Finset V) (hR : ∀ v, ∃ w ∈ R, G.Reachable v w) :
    compCount G ≤ R.card := by
  classical
  have hs : Function.Surjective (fun w : R ↦ G.connectedComponentMk w.val) := by
    intro c
    induction c using ConnectedComponent.ind with
    | _ v =>
      obtain ⟨w, hw, hr⟩ := hR v
      exact ⟨⟨w, hw⟩, Quot.sound hr.symm⟩
  simpa [compCount] using Fintype.card_le_of_surjective _ hs

theorem common_compCount_le_three (a b : Pattern k) :
    compCount (common a.val b.val) ≤ 3 := by
  classical
  let M := (doublePaths a.val b.val).image (middleRep a.val b.val)
  have hM : M.card ≤ (doublePaths a.val b.val).card := card_image_le
  by_cases full : ∃ p, a.val p = uncut k ∧ b.val p = uncut k
  · obtain ⟨p, ha, hb⟩ := full
    have ht := (reachable_terminals a.val b.val p ha hb).symm
    have H := compCount_le_of_representatives (insert (start k) M) (G := common a.val b.val)
      (fun v ↦ by
        rcases reachable_representative a.val b.val v with h | h | ⟨q, hq, hr⟩
        · exact ⟨start k, mem_insert_self _ _, h⟩
        · exact ⟨start k, mem_insert_self _ _, h.trans ht⟩
        · exact ⟨middleRep a.val b.val q, mem_insert_of_mem (mem_image_of_mem _ hq), hr⟩)
    have hc := card_insert_le (a := start k) (s := M)
    have hd := card_doublePaths_le_two a b
    omega
  · have H := compCount_le_of_representatives (insert (start k) (insert (finish k) M))
      (G := common a.val b.val) (fun v ↦ by
        rcases reachable_representative a.val b.val v with h | h | ⟨q, hq, hr⟩
        · exact ⟨start k, mem_insert_self _ _, h⟩
        · exact ⟨finish k, mem_insert_of_mem (mem_insert_self _ _), h⟩
        · exact ⟨middleRep a.val b.val q,
            mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ hq)), hr⟩)
    have hc := card_insert_le (a := start k) (s := insert (finish k) M)
    have ht := card_insert_le (a := finish k) (s := M)
    have hd := card_doublePaths_le_one a b full
    omega

end Theta359778
```

## ThetaFamily.lean

```lean
import ThetaReach
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace Theta359778

open SimpleGraph Finset

noncomputable def fullChoicesEquiv (k : ℕ) :
    {a : Choices k // ¬ ∃ p, a p = uncut k} ≃ (Fin 3 → Fin (k + 2)) where
  toFun a p := ⟨(a.val p).val, by
    have h := a.property
    by_contra! hn
    exact h ⟨p, Fin.ext (by have := (a.val p).isLt; simp [uncut]; omega)⟩⟩
  invFun b := ⟨fun p ↦ (b p).castSucc, by
    rintro ⟨p, hp⟩
    have h := congrArg Fin.val hp
    have hb := (b p).isLt
    simp [uncut] at h
    omega⟩
  left_inv a := Subtype.ext (funext fun _ ↦ rfl)
  right_inv b := funext fun _ ↦ rfl

theorem card_pattern (k : ℕ) [Fintype (Pattern k)] :
    Fintype.card (Pattern k) = 1 + 3 * (k + 2) + 3 * (k + 2)^2 := by
  classical
  have h := Fintype.card_subtype_compl (fun a : Choices k ↦ ∃ p, a p = uncut k)
  rw [Fintype.card_congr (fullChoicesEquiv k)] at h
  simp only [Choices, Fintype.card_fun, Fintype.card_fin] at h
  have he : (k + 3)^3 =
      (k + 2)^3 + (1 + 3 * (k + 2) + 3 * (k + 2)^2) := by ring
  change (k + 2)^3 = (k + 3)^3 - Fintype.card (Pattern k) at h
  rw [he] at h
  have hp : 0 < (k + 2)^3 := pow_pos (by omega) _
  omega

def free (k : ℕ) : Finset (Sym2 (Vertex k)) :=
  (⊤ : SimpleGraph (Vertex k)).edgeFinset \ core k

theorem card_free (k : ℕ) :
    (free k).card = (3 * (k + 2) - 1).choose 2 - 3 * (k + 2) := by
  rw [free, card_sdiff_of_subset (core_subset_top k), card_edgeFinset_top_eq_card_choose_two,
    card_core, card_vertex]

theorem common_subset_core (a b : Choices k) :
    (common a b).edgeSet ⊆ (core k : Set (Sym2 (Vertex k))) := by
  intro e he
  rw [common, edgeSet_fromEdgeSet] at he
  obtain ⟨i, rfl, _, _⟩ := he.1
  exact edge_mem_core i

theorem common_index_iff (a b : Choices k) (i : Index k) :
    edge k i ∈ (common a b).edgeSet ↔
      i.2.val ≠ (a i.1).val ∧ i.2.val ≠ (b i.1).val := by
  rw [common, edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨⟨j, hj, h₁, h₂⟩, _⟩
    obtain rfl := edge_injective k hj
    exact ⟨h₁, h₂⟩
  · intro h
    exact ⟨⟨i, rfl, h⟩, edge_not_diag i⟩

abbrev FamilyData (k : ℕ) :=
  Pattern k × {T : Finset (Sym2 (Vertex k)) // T ∈ (free k).powerset}

def makeGraph (k : ℕ) (d : FamilyData k) : SimpleGraph (Vertex k) :=
  fromEdgeSet ((common d.1.val d.1.val).edgeSet ∪ (d.2.val : Set (Sym2 (Vertex k))))

theorem makeGraph_edgeSet (d : FamilyData k) :
    (makeGraph k d).edgeSet =
      (common d.1.val d.1.val).edgeSet ∪ (d.2.val : Set (Sym2 (Vertex k))) := by
  rw [makeGraph, edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he ↦ he.1
  intro he
  refine ⟨he, fun hd ↦ ?_⟩
  rcases he with he | he
  · exact not_isDiag_of_mem_edgeSet _ he hd
  · have he' := (mem_powerset.mp d.2.property) (show e ∈ d.2.val from he)
    exact not_isDiag_of_mem_edgeFinset (mem_sdiff.mp he').1 hd

theorem makeGraph_index_iff (d : FamilyData k) (i : Index k) :
    edge k i ∈ (makeGraph k d).edgeSet ↔ i.2.val ≠ (d.1.val i.1).val := by
  rw [makeGraph_edgeSet, Set.mem_union, common_index_iff, and_self]
  have h : edge k i ∉ d.2.val := fun he ↦
    (mem_sdiff.mp (mem_powerset.mp d.2.property he)).2 (edge_mem_core i)
  simp [h]

theorem makeGraph_free_iff (d : FamilyData k) {e : Sym2 (Vertex k)}
    (he : e ∈ free k) :
    e ∈ (makeGraph k d).edgeSet ↔ e ∈ d.2.val := by
  rw [makeGraph_edgeSet, Set.mem_union]
  have h : e ∉ (common d.1.val d.1.val).edgeSet :=
    fun hc ↦ (mem_sdiff.mp he).2 (common_subset_core _ _ hc)
  simp [h]

theorem makeGraph_injective (k : ℕ) : Function.Injective (makeGraph k) := by
  intro d e h
  apply Prod.ext
  · apply Subtype.ext
    funext p
    have left (d e : FamilyData k) (h : makeGraph k d = makeGraph k e)
        (hd : (d.1.val p).val < k + 2) : d.1.val p = e.1.val p := by
      let i : Index k := (p, ⟨(d.1.val p).val, hd⟩)
      have H : edge k i ∉ (makeGraph k d).edgeSet :=
        fun hi ↦ makeGraph_index_iff d i |>.mp hi rfl
      rw [h, makeGraph_index_iff] at H
      exact Fin.ext (not_not.mp H)
    by_cases hd : (d.1.val p).val < k + 2
    · exact left d e h hd
    by_cases he : (e.1.val p).val < k + 2
    · exact (left e d h.symm he).symm
    apply Fin.ext
    have hd' := (d.1.val p).isLt
    have he' := (e.1.val p).isLt
    omega
  · apply Subtype.ext
    ext x
    by_cases hx : x ∈ free k
    · rw [← makeGraph_free_iff d hx, ← makeGraph_free_iff e hx, h]
    · have hd : x ∉ d.2.val := fun hd ↦ hx (mem_powerset.mp d.2.property hd)
      have he : x ∉ e.2.val := fun he ↦ hx (mem_powerset.mp e.2.property he)
      simp [hd, he]

theorem common_le_inf (d e : FamilyData k) :
    common d.1.val e.1.val ≤ makeGraph k d ⊓ makeGraph k e := by
  intro v w hw
  obtain ⟨i, hi, hd, he⟩ := ((fromEdgeSet_adj _).mp hw).1
  exact ⟨(mem_edgeSet (G := makeGraph k d)).mp (hi ▸ (makeGraph_index_iff d i).mpr hd),
    (mem_edgeSet (G := makeGraph k e)).mp (hi ▸ (makeGraph_index_iff e i).mpr he)⟩

noncomputable def family (k : ℕ) : Finset (SimpleGraph (Vertex k)) := by
  classical
  exact univ.map ⟨makeGraph k, makeGraph_injective k⟩

theorem family_card (k : ℕ) :
    (family k).card =
      (1 + 3 * (k + 2) + 3 * (k + 2)^2) *
        2^((3 * (k + 2) - 1).choose 2 - 3 * (k + 2)) := by
  classical
  rw [family, card_map, card_univ, Fintype.card_prod, card_pattern, Fintype.card_coe,
    card_powerset, card_free]

theorem family_pair (k : ℕ) (G H : SimpleGraph (Vertex k))
    (hG : G ∈ family k) (hH : H ∈ family k) :
    compCount (G ⊓ H) ≤ 3 := by
  classical
  obtain ⟨d, -, rfl⟩ := mem_map.mp hG
  obtain ⟨e, -, rfl⟩ := mem_map.mp hH
  exact (compCount_le_of_le (common_le_inf d e)).trans (common_compCount_le_three d.1 e.1)

end Theta359778
```

## ThetaRefutation.lean

```lean
import ThetaFamily
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

namespace Theta359778

open SimpleGraph Finset

/-- Graphs are simple and retain all labelled vertices under intersection. -/
def Valid {n : ℕ} (F : Finset (SimpleGraph (Fin n))) : Prop :=
  ∀ G ∈ F, ∀ H ∈ F, compCount (G ⊓ H) ≤ 3

/-- The right-hand side of Leader–Ranđelović–Tan, Conjecture 7. -/
def bound (n : ℕ) : ℚ :=
  (n + 3 : ℚ)^2 / 8 * (1 / 2^n) * 2^(n.choose 2)

/-- Conjecture 7, with the bound interpreted as a rational number. -/
def Conjecture : Prop :=
  ∀ n : ℕ, Odd n → ∀ F : Finset (SimpleGraph (Fin n)), Valid F → (F.card : ℚ) ≤ bound n

theorem bound_lt_iff (n c : ℕ) :
    bound n < (c : ℚ) ↔
      (n + 3)^2 * 2^(n.choose 2) < 8 * 2^n * c := by
  have h : 0 < (8 : ℚ) * 2^n := by positivity
  have ht : bound n = (n + 3 : ℚ)^2 * 2^(n.choose 2) / (8 * 2^n) := by
    unfold bound
    ring
  rw [ht, div_lt_iff₀ h, mul_comm (c : ℚ)]
  exact_mod_cast Iff.rfl

theorem strict_comparison (h n : ℕ) (hh : 1 ≤ h) (hn : n = 6*h - 1)
    (hq : 6*h ≤ n.choose 2) :
    bound n < ((1 + 6*h + 12*h^2) * 2^(n.choose 2 - 6*h) : ℕ) := by
  apply (bound_lt_iff n _).mpr
  have hn' : n + 1 = 6*h := by omega
  have hadd : (n + 1) + (n.choose 2 - 6*h) = n.choose 2 := by omega
  have hpow : (2 : ℕ)^n * 2 * 2^(n.choose 2 - 6*h) = 2^(n.choose 2) := by
    rw [← pow_succ, ← pow_add, hadd]
  have hlin : n + 3 = 2 * (3*h + 1) := by omega
  have hp : 0 < h^2 := pow_pos (by omega) _
  have hgap : 1 + 6*h + 12*h^2 = (3*h + 1)^2 + 3*h^2 := by ring
  have hcoef : (3*h + 1)^2 < 1 + 6*h + 12*h^2 := by omega
  have hl : (n + 3)^2 * 2^(n.choose 2) =
      4 * ((3*h + 1)^2 * 2^(n.choose 2)) := by rw [hlin]; ring
  have hr : 8 * 2^n * ((1 + 6*h + 12*h^2) * 2^(n.choose 2 - 6*h)) =
      4 * ((1 + 6*h + 12*h^2) * 2^(n.choose 2)) := by rw [← hpow]; ring
  rw [hl, hr]
  exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hcoef (by positivity)) (by decide)

/-- Relabel vertices while preserving the component count. -/
theorem compCount_overFin {V : Type} [Fintype V] (G : SimpleGraph V) {n : ℕ}
    (hc : Fintype.card V = n) : compCount (G.overFin hc) = compCount G := by
  classical
  simpa only [compCount, ← Nat.card_eq_fintype_card] using
    Nat.card_congr (G.overFinIso hc).connectedComponentEquiv.symm

theorem core_fits (h : ℕ) (hh : 1 ≤ h) : 6*h ≤ (6*h - 1).choose 2 := by
  let k := 2*h - 2
  have hk : k + 2 = 2*h := by dsimp [k]; omega
  have hq := Finset.card_le_card (core_subset_top k)
  rw [card_core, card_edgeFinset_top_eq_card_choose_two, card_vertex, hk] at hq
  have he : 3 * (2*h) = 6*h := by omega
  simpa only [he] using hq

/-- Equal-length theta paths give the explicit family at every order `6*h - 1`. -/
theorem theta_family (h : ℕ) (hh : 1 ≤ h) :
    ∃ F : Finset (SimpleGraph (Fin (6*h - 1))),
      Valid F ∧
      F.card = (1 + 6*h + 12*h^2) * 2^((6*h - 1).choose 2 - 6*h) ∧
      bound (6*h - 1) < (F.card : ℚ) := by
  classical
  let n := 6*h - 1
  let k := 2*h - 2
  have hk : k + 2 = 2*h := by dsimp [k]; omega
  have hc : Fintype.card (Vertex k) = n := by dsimp [n]; rw [card_vertex, hk]; omega
  let e := (Fintype.equivFinOfCardEq hc).simpleGraph
  let F := (family k).map e.toEmbedding
  have hcard : F.card = (1 + 6*h + 12*h^2) * 2^(n.choose 2 - 6*h) := by
    dsimp only [F]
    rw [card_map, family_card, hk]
    have hn : 3 * (2*h) - 1 = n := by dsimp [n]; omega
    have hmul : 3 * (2*h) = 6*h := by ring
    have hsq : 3 * (2*h)^2 = 12*h^2 := by ring
    rw [hn, hmul, hsq]
  refine ⟨F, ?_, hcard, ?_⟩
  · intro G hG H hH
    obtain ⟨G', hG', rfl⟩ := mem_map.mp hG
    obtain ⟨H', hH', rfl⟩ := mem_map.mp hH
    change compCount ((G' ⊓ H').overFin hc) ≤ 3
    rw [compCount_overFin]
    exact family_pair k G' H' hG' hH'
  · rw [hcard]
    exact strict_comparison h n hh rfl (core_fits h hh)

theorem odd_order (h : ℕ) (hh : 1 ≤ h) : Odd (6*h - 1) := by
  exact ⟨3*h - 1, by omega⟩

/-- The reviewed large-order endpoint, with the positive denominator cleared. -/
theorem lrt_conj7_fails (N : ℕ) :
    ∃ n > N, Odd n ∧ ∃ F : Finset (SimpleGraph (Fin n)),
      Valid F ∧ (n + 3)^2 * 2^(n.choose 2) < 8 * 2^n * F.card := by
  let h := N + 1
  have hh : 1 ≤ h := by dsimp [h]; omega
  obtain ⟨F, hv, _, hb⟩ := theta_family h hh
  exact ⟨6*h - 1, by dsimp [h]; omega, odd_order h hh, F, hv, (bound_lt_iff _ _).mp hb⟩

/-- Literal negation of the source conjecture, using the theta family. -/
theorem not_conjecture : ¬ Conjecture := by
  intro hc
  obtain ⟨F, hv, _, hb⟩ := theta_family 1 (by decide)
  exact (not_le_of_gt hb) (hc _ (odd_order 1 (by decide)) F hv)

/-- The first order in the infinite series. -/
theorem five_vertex_counterexample :
    ∃ F : Finset (SimpleGraph (Fin 5)), Valid F ∧ F.card = 304 ∧ bound 5 = 256 := by
  obtain ⟨F, hv, hc, _⟩ := theta_family 1 (by decide)
  refine ⟨F, hv, ?_, ?_⟩
  · exact hc.trans (by decide)
  · norm_num [bound, Nat.choose]

#check Conjecture
set_option pp.funBinderTypes true in
#check theta_family
set_option pp.funBinderTypes true in
#check lrt_conj7_fails
#check not_conjecture
set_option pp.funBinderTypes true in
#check five_vertex_counterexample
#print axioms theta_family
#print axioms lrt_conj7_fails
#print axioms not_conjecture
#print axioms five_vertex_counterexample

end Theta359778
```

## ThetaRatio.lean

```lean
import ThetaRefutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

namespace Theta359778

open SimpleGraph Filter
open scoped Topology

theorem bound_factor (h : ℕ) (hh : 1 ≤ h) :
    bound (6*h - 1) =
      (3*(h : ℚ) + 1)^2 * 2^((6*h - 1).choose 2 - 6*h) := by
  let n := 6*h - 1
  have hq : 6*h ≤ n.choose 2 := core_fits h hh
  have hsum : n.choose 2 = n + 1 + (n.choose 2 - 6*h) := by dsimp [n] at *; omega
  have hn : n + 3 = 2 * (3*h + 1) := by dsimp [n]; omega
  have hn' : (n : ℚ) + 3 = 2 * (3*(h : ℚ) + 1) := by exact_mod_cast hn
  have hp : (2 : ℚ)^n.choose 2 = 2^n * 2 * 2^(n.choose 2 - 6*h) := by
    conv_lhs => rw [hsum]
    rw [pow_add, pow_succ]
  change bound n = _
  unfold bound
  rw [hn', hp]
  have hne : (2 : ℚ)^n ≠ 0 := by positivity
  field_simp
  ring

theorem cardinal_ratio (h c : ℕ) (hh : 1 ≤ h)
    (hc : c = (1 + 6*h + 12*h^2) * 2^((6*h - 1).choose 2 - 6*h)) :
    (c : ℚ) / bound (6*h - 1) =
      (1 + 6*(h : ℚ) + 12*(h : ℚ)^2) / (3*(h : ℚ) + 1)^2 := by
  rw [hc, bound_factor h hh]
  push_cast
  exact mul_div_mul_right _ _ (by positivity)

theorem ratio_tendsto :
    Tendsto (fun h : ℕ ↦
      (1 + 6*(h : ℝ) + 12*(h : ℝ)^2) / (3*(h : ℝ) + 1)^2) atTop (𝓝 (4/3 : ℝ)) := by
  have hi : Tendsto (fun h : ℕ ↦ (h : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hnum := ((hi.pow 2).add ((tendsto_const_nhds (x := (6 : ℝ))).mul hi)).add
    (tendsto_const_nhds (x := (12 : ℝ)))
  have hden := ((tendsto_const_nhds (x := (3 : ℝ))).add hi).pow 2
  have hlim := hnum.div hden (by norm_num)
  have H : Tendsto (fun h : ℕ ↦
      (((h : ℝ)⁻¹)^2 + 6*(h : ℝ)⁻¹ + 12) / (3 + (h : ℝ)⁻¹)^2) atTop (𝓝 (4/3 : ℝ)) := by
    convert hlim using 2
    all_goals norm_num
  refine H.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
  have h0 : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have hd : (3 : ℝ) * h + 1 ≠ 0 := by positivity
  field_simp

#check cardinal_ratio
#check ratio_tendsto
#print axioms cardinal_ratio
#print axioms ratio_tendsto

end Theta359778
```

