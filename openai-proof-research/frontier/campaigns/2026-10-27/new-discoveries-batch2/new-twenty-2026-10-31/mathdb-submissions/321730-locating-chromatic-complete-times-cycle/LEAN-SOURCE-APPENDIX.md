# Lean source appendix for MathDB 321730

The ten modules appear in import order.

### `LocatingStatement.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Fintype.EquivFin

open SimpleGraph

namespace Locating321730

variable {V : Type*} {k : ℕ}

noncomputable def colorDist (G : SimpleGraph V) (c : V → Fin k)
    (v : V) (x : Fin k) : ℕ :=
  sInf {d | ∃ w : V, c w = x ∧ G.dist v w = d}

def IsLocating (G : SimpleGraph V) (c : V → Fin k) : Prop :=
  (∀ u v, G.Adj u v → c u ≠ c v) ∧ Function.Surjective c ∧
  Function.Injective (fun v => fun x => colorDist G c v x)

noncomputable def locChrom (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ c : V → Fin k, IsLocating G c}

def KC (m n : ℕ) : SimpleGraph (Fin m × Fin n) :=
  (⊤ : SimpleGraph (Fin m)).boxProd (SimpleGraph.cycleGraph n)

def KP (m n : ℕ) : SimpleGraph (Fin m × Fin n) :=
  (⊤ : SimpleGraph (Fin m)).boxProd (SimpleGraph.pathGraph n)

variable {G : SimpleGraph V} {c : V → Fin k} {v w : V} {x : Fin k}

theorem colorDist_le (hw : c w = x) : colorDist G c v x ≤ G.dist v w :=
  csInf_le' (show G.dist v w ∈ {d | ∃ u : V, c u = x ∧ G.dist v u = d} from ⟨w, hw, rfl⟩)

theorem colorDist_attained (hx : ∃ w, c w = x) :
    ∃ w, c w = x ∧ G.dist v w = colorDist G c v x := by
  obtain ⟨w, hw⟩ := hx
  exact csInf_mem (show ({d | ∃ w : V, c w = x ∧ G.dist v w = d} : Set ℕ).Nonempty
    from ⟨G.dist v w, w, hw, rfl⟩)

theorem colorDist_own : colorDist G c v (c v) = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using colorDist_le (v := v) (rfl : c v = c v))

theorem colorDist_eq_zero_iff (hG : G.Preconnected) (hs : Function.Surjective c) :
    colorDist G c v x = 0 ↔ c v = x := by
  constructor
  · intro h
    obtain ⟨w, hw, hd⟩ := colorDist_attained (v := v) (hs x)
    exact ((hG v w).dist_eq_zero_iff.mp (hd.trans h)) ▸ hw
  · rintro rfl
    exact colorDist_own

theorem colorDist_eq_one_iff (hG : G.Preconnected) (hs : Function.Surjective c)
    (hx : c v ≠ x) : colorDist G c v x = 1 ↔ ∃ w, c w = x ∧ G.Adj v w := by
  constructor
  · intro h
    obtain ⟨w, hw, hd⟩ := colorDist_attained (v := v) (hs x)
    exact ⟨w, hw, dist_eq_one_iff_adj.mp (hd.trans h)⟩
  · rintro ⟨w, hw, ha⟩
    have hle := colorDist_le (G := G) (v := v) hw
    rw [dist_eq_one_iff_adj.mpr ha] at hle
    have hne := mt (colorDist_eq_zero_iff hG hs).mp hx
    omega

theorem colorDist_singleton (hw : ∀ u, c u = x ↔ u = w) :
    colorDist G c v x = G.dist v w := by
  obtain ⟨u, hu, hd⟩ := colorDist_attained (G := G) (v := v) ⟨w, (hw w).mpr rfl⟩
  rw [(hw u).mp hu] at hd
  exact hd.symm

theorem locating_exists [Fintype V] (hG : G.Preconnected) :
    ∃ c : V → Fin (Fintype.card V), IsLocating G c := by
  let c := Fintype.equivFin V
  refine ⟨c, fun u v h e => G.ne_of_adj h (c.injective e), c.surjective, ?_⟩
  intro u v h
  have he := congrFun h (c u)
  change colorDist G c u (c u) = colorDist G c v (c u) at he
  rw [colorDist_own] at he
  exact c.injective ((colorDist_eq_zero_iff hG c.surjective).mp he.symm).symm

theorem locChrom_attained [Fintype V] (hG : G.Preconnected) :
    ∃ c : V → Fin (locChrom G), IsLocating G c :=
  csInf_mem (show ({k | ∃ c : V → Fin k, IsLocating G c} : Set ℕ).Nonempty
    from ⟨Fintype.card V, locating_exists hG⟩)

theorem locChrom_le (hc : IsLocating G c) : locChrom G ≤ k :=
  csInf_le' (show k ∈ {k | ∃ c : V → Fin k, IsLocating G c} from ⟨c, hc⟩)

theorem KC_connected {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : (KC m n).Connected := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨preconnected_top.boxProd cycleGraph_preconnected⟩

theorem KP_connected {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : (KP m n).Connected := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨preconnected_top.boxProd (pathGraph_preconnected n)⟩

/-- The proposition printed as Conjecture 3, with independent eventual thresholds. -/
def Conjecture321730 : Prop :=
  ∃ M N : ℕ, ∀ m n : ℕ, M ≤ m → N ≤ n →
    locChrom (KC m n) = locChrom (KP m n)

#print Conjecture321730
#print axioms Conjecture321730
#print axioms locChrom_attained
#print axioms KC_connected
#print axioms KP_connected

end Locating321730
```

### `LocatingMetric.lean`

```lean
import LocatingStatement

open SimpleGraph

namespace Locating321730

variable {m n : ℕ}

/-- Absolute difference of the linear column indices. -/
def gap (a b : Fin n) : ℕ := a.val - b.val + (b.val - a.val)

theorem gap_comm (a b : Fin n) : gap a b = gap b a := Nat.add_comm _ _

theorem path_adj_iff_gap (a b : Fin n) : (pathGraph n).Adj a b ↔ gap a b = 1 := by
  rw [pathGraph_adj, gap]
  omega

theorem cycle_adj_iff_gap (hn : 2 ≤ n) (a b : Fin n) :
    (cycleGraph n).Adj a b ↔ gap a b = 1 ∨ gap a b + 1 = n := by
  have hsub (x y : Fin n) :
      (x - y).val = if y.val ≤ x.val then x.val - y.val else n - (y.val - x.val) := by
    rw [Fin.val_sub]
    have hx := x.isLt
    have hy := y.isLt
    split
    · rename_i h
      rw [show n - y.val + x.val = (x.val - y.val) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · rename_i h
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  rw [cycleGraph_adj', hsub, hsub, gap]
  have ha := a.isLt
  have hb := b.isLt
  split <;> split <;> omega

theorem path_dist_le_of_le (a b : Fin n) (hab : a.val ≤ b.val) :
    (pathGraph n).dist a b ≤ b.val - a.val := by
  generalize h : b.val - a.val = d
  induction d generalizing b with
  | zero =>
    have : b = a := Fin.ext (by omega)
    subst b
    simp
  | succ d ih =>
    let p : Fin n := ⟨b.val - 1, by omega⟩
    have hp : p.val + 1 = b.val := by
      change b.val - 1 + 1 = b.val
      omega
    have hpb : (pathGraph n).Adj p b := pathGraph_adj.mpr (Or.inl hp)
    have hle := ih p (by omega) (by omega)
    have ht := (pathGraph_preconnected n a p).dist_triangle_left b
    rw [dist_eq_one_iff_adj.mpr hpb] at ht
    omega

theorem path_dist (a b : Fin n) : (pathGraph n).dist a b = gap a b := by
  apply le_antisymm
  · by_cases hab : a.val ≤ b.val
    · have := path_dist_le_of_le a b hab
      unfold gap
      omega
    · rw [dist_comm, gap_comm]
      have := path_dist_le_of_le b a (by omega)
      unfold gap
      omega
  · obtain ⟨p, hp⟩ := (pathGraph_preconnected n a b).exists_walk_length_eq_dist
    rw [← hp]
    clear hp
    induction p with
    | nil => simp [gap]
    | cons h p ih =>
      rw [Walk.length_cons]
      rw [pathGraph_adj] at h
      unfold gap at *
      omega

def cycleGap (a b : Fin n) : ℕ := min (gap a b) (n - gap a b)

theorem cycle_dist (hn : 2 ≤ n) (a b : Fin n) :
    (cycleGraph n).dist a b = cycleGap a b := by
  apply le_antisymm
  · have upper (u v : Fin n) : (cycleGraph n).dist u v ≤ gap u v := by
      rw [← path_dist]
      exact (pathGraph_preconnected n u v).dist_anti pathGraph_le_cycleGraph
    have wrap (u v : Fin n) (huv : u.val ≤ v.val) :
        (cycleGraph n).dist u v ≤ n - gap u v := by
      let lo : Fin n := ⟨0, by omega⟩
      let hi : Fin n := ⟨n - 1, by omega⟩
      have hEdge : (cycleGraph n).Adj lo hi := (cycle_adj_iff_gap hn lo hi).2 (Or.inr (by
        change 0 - (n - 1) + (n - 1 - 0) + 1 = n
        omega))
      have h₁ := upper u lo
      have h₂ := upper hi v
      have h₃ := (cycleGraph_preconnected (n := n) u lo).dist_triangle_left v
      have h₄ := hEdge.reachable.dist_triangle_left v
      rw [dist_eq_one_iff_adj.mpr hEdge] at h₄
      unfold gap at h₁ h₂ ⊢
      change u.val - 0 + (0 - u.val) ≥ _ at h₁
      change n - 1 - v.val + (v.val - (n - 1)) ≥ _ at h₂
      have := v.isLt
      omega
    refine le_min (upper a b) ?_
    by_cases h : a.val ≤ b.val
    · exact wrap a b h
    · rw [dist_comm, gap_comm]
      exact wrap b a (by omega)
  · obtain ⟨p, hp⟩ := (cycleGraph_preconnected (n := n) a b).exists_walk_length_eq_dist
    rw [← hp]
    clear hp
    induction p with
    | nil => simp [cycleGap, gap]
    | @cons u v w h p ih =>
      rw [Walk.length_cons]
      rw [cycle_adj_iff_gap hn] at h
      have hu := u.isLt
      have hv := v.isLt
      have hw := w.isLt
      simp only [cycleGap, gap, Nat.min_def] at *
      split at ih <;> split <;> omega

theorem product_dist {H : SimpleGraph (Fin n)} (hc : H.Preconnected)
    (a b : Fin m × Fin n) :
    ((⊤ : SimpleGraph (Fin m)).boxProd H).dist a b =
      (if a.1 = b.1 then 0 else 1) + H.dist a.2 b.2 := by
  have ht : (⊤ : SimpleGraph (Fin m)).Preconnected := preconnected_top
  rw [← dist_top]
  exact_mod_cast (show
    (((⊤ : SimpleGraph (Fin m)).boxProd H).dist a b : ℕ∞) =
      ((⊤ : SimpleGraph (Fin m)).dist a.1 b.1 : ℕ∞) + (H.dist a.2 b.2 : ℕ∞) by
        rw [(ht.boxProd hc a b).coe_dist_eq_edist, (ht a.1 b.1).coe_dist_eq_edist,
          (hc a.2 b.2).coe_dist_eq_edist, edist_boxProd])

#print axioms path_dist
#print axioms cycle_dist
#print axioms product_dist

end Locating321730
```

### `LocatingLowerCore.lean`

```lean
import LocatingMetric

open SimpleGraph

namespace Locating321730

variable {m n k : ℕ} {H : SimpleGraph (Fin n)}

abbrev Grid (m : ℕ) (H : SimpleGraph (Fin n)) := (⊤ : SimpleGraph (Fin m)).boxProd H

def Present (c : Fin m × Fin n → Fin k) (z : Fin k) (j : Fin n) : Prop :=
  ∃ i, c (i, j) = z

abbrev Proper (G : SimpleGraph V) (c : V → Fin k) := ∀ u v, G.Adj u v → c u ≠ c v

theorem column_injective {c : Fin m × Fin n → Fin k} (hc : Proper (Grid m H) c)
    (j : Fin n) : Function.Injective (fun i => c (i, j)) := by
  intro i i' he
  by_contra hne
  exact hc (i, j) (i', j) (Or.inl ⟨hne, rfl⟩) he

theorem column_dist {c : Fin m × Fin n → Fin k} {j : Fin n} {i : Fin m} {x : Fin k}
    (hH : H.Preconnected) (hs : Function.Surjective c) (hp : Present c x j) :
    colorDist (Grid m H) c (i, j) x = if c (i, j) = x then 0 else 1 := by
  split
  · rename_i h
    exact (colorDist_eq_zero_iff (preconnected_top.boxProd hH) hs).2 h
  · rename_i hn
    obtain ⟨r, hr⟩ := hp
    have hne : i ≠ r := fun he => hn (he ▸ hr)
    exact (colorDist_eq_one_iff (preconnected_top.boxProd hH) hs hn).2
      ⟨(r, j), hr, Or.inl ⟨hne, rfl⟩⟩

theorem missing_exists {c : Fin m × Fin n → Fin (m + 1)} (hc : Proper (Grid m H) c)
    (j : Fin n) : ∃ z, ¬ Present c z j := by
  by_contra! h
  have hb : Function.Bijective (fun i => c (i, j)) := ⟨column_injective hc j, h⟩
  have := Fintype.card_congr (Equiv.ofBijective _ hb)
  simp at this

theorem present_of_ne_missing {c : Fin m × Fin n → Fin (m + 1)}
    (hc : Proper (Grid m H) c) {j : Fin n} {z x : Fin (m + 1)}
    (hz : ¬ Present c z j) (hx : x ≠ z) : Present c x j := by
  classical
  let f : Fin m → ↥((Finset.univ : Finset (Fin (m + 1))).erase z) :=
    fun i => ⟨c (i, j), Finset.mem_erase.mpr ⟨fun h => hz ⟨i, h⟩, Finset.mem_univ _⟩⟩
  have hi : Function.Injective f := fun _ _ e => column_injective hc j (congrArg Subtype.val e)
  have hcard : Fintype.card (Fin m) = Fintype.card ↥((Finset.univ : Finset (Fin (m + 1))).erase z) := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have hb := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hi, hcard⟩
  obtain ⟨i, hi⟩ := hb.2 ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem only_missing_coordinate {c : Fin m × Fin n → Fin (m + 1)}
    (hH : H.Preconnected) (hc : IsLocating (Grid m H) c) {v w : Fin m × Fin n} {z : Fin (m + 1)}
    (hv : ¬ Present c z v.2) (hw : ¬ Present c z w.2) (hcol : c v = c w)
    (hz : colorDist (Grid m H) c v z = colorDist (Grid m H) c w z) : v = w := by
  apply hc.2.2
  funext x
  by_cases hx : x = z
  · simpa [hx] using hz
  · change colorDist (Grid m H) c (v.1, v.2) x = colorDist (Grid m H) c (w.1, w.2) x
    rw [column_dist hH hc.2.1 (present_of_ne_missing hc.1 hv hx),
      column_dist hH hc.2.1 (present_of_ne_missing hc.1 hw hx), hcol]

def Colorful (G : SimpleGraph V) (c : V → Fin k) (v : V) : Prop :=
  ∀ x, colorDist G c v x = if c v = x then 0 else 1

theorem colorful_injective {G : SimpleGraph V} {c : V → Fin k} (hc : IsLocating G c)
    {v w : V} (hv : Colorful G c v) (hw : Colorful G c w) (h : c v = c w) : v = w := by
  apply hc.2.2
  funext x
  change colorDist G c v x = colorDist G c w x
  rw [hv x, hw x, h]

theorem clique_lower (hH : H.Preconnected) (hm : 0 < m) (hn : 2 ≤ n)
    {c : Fin m × Fin n → Fin k} (hc : IsLocating (Grid m H) c) : m + 1 ≤ k := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hle : m ≤ k := by
    simpa using Fintype.card_le_of_injective _ (column_injective hc.1 a)
  by_contra! h
  have he : m = k := by omega
  have hp (j : Fin n) (x : Fin k) : Present c x j :=
    ((Fintype.bijective_iff_injective_and_card (fun i => c (i, j))).mpr
      ⟨column_injective hc.1 j, by simpa using he⟩).2 x
  have hj (v : Fin m × Fin n) : Colorful (Grid m H) c v :=
    fun x => column_dist hH hc.2.1 (hp v.2 x)
  let i : Fin m := ⟨0, hm⟩
  obtain ⟨r, hr⟩ := hp b (c (i, a))
  have h := colorful_injective hc (hj (r, b)) (hj (i, a)) hr
  have hab := congrArg (fun v : Fin m × Fin n => v.2.val) h
  contradiction

theorem bounded_run_impossible {c : Fin m × Fin n → Fin (m + 1)}
    (hH : H.Preconnected) (hc : IsLocating (Grid m H) c) (hm : 3 ≤ m)
    {z : Fin (m + 1)} {L : ℕ} (hL : 2 ≤ L)
    (col : Fin L → Fin n) (hcol : Function.Injective col)
    (hmiss : ∀ t, ¬ Present c z (col t))
    (hbound : ∀ i t, colorDist (Grid m H) c (i, col t) z ≤ (L + 1) / 2 + 1)
    (v₀ v₁ : Fin m × Fin n)
    (hboundary : ∀ i t, colorDist (Grid m H) c (i, col t) z = 1 →
      (i, col t) = v₀ ∨ (i, col t) = v₁) : False := by
  classical
  let D := (L + 1) / 2 + 1
  let colors := {x : Fin (m + 1) // x ∈ Finset.univ.erase z}
  have hxp (x : colors) : x.val ≠ z := (Finset.mem_erase.mp x.property).1
  let r (x : colors) (t : Fin L) : Fin m :=
    Classical.choose (present_of_ne_missing hc.1 (hmiss t) (hxp x))
  have hr (x : colors) (t : Fin L) : c (r x t, col t) = x.val :=
    Classical.choose_spec (present_of_ne_missing hc.1 (hmiss t) (hxp x))
  let δ (x : colors) (t : Fin L) := colorDist (Grid m H) c (r x t, col t) z
  have hpos (x : colors) (t : Fin L) : 0 < δ x t :=
    Nat.pos_of_ne_zero fun e => hmiss t ⟨r x t,
      (colorDist_eq_zero_iff (preconnected_top.boxProd hH) hc.2.1).mp e⟩
  have hδ (x : colors) : Function.Injective (δ x) := by
    intro t s he
    have hv := only_missing_coordinate hH hc (hmiss t) (hmiss s) ((hr x t).trans (hr x s).symm) he
    exact hcol (congrArg Prod.snd hv)
  have hcard : Fintype.card colors = m := by
    change Fintype.card {x : Fin (m + 1) // x ∈ Finset.univ.erase z} = m
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  let x₀ : colors := Fintype.equivFin colors |>.symm ⟨0, by omega⟩
  let f (t : Fin L) : Fin D := ⟨δ x₀ t - 1, by
    have := hbound (r x₀ t) t
    change δ x₀ t ≤ D at this
    have := hpos x₀ t
    omega⟩
  have hinj : Function.Injective f := by
    intro t s e
    have he := congrArg Fin.val e
    change δ x₀ t - 1 = δ x₀ s - 1 at he
    exact hδ x₀ (by have := hpos x₀ t; have := hpos x₀ s; omega)
  have hle : L ≤ D := by simpa using Fintype.card_le_of_injective f hinj
  have hDL : D = L := by dsimp [D] at *; omega
  have hone (x : colors) : ∃ t, δ x t = 1 := by
    let g (t : Fin L) : Fin L := ⟨δ x t - 1, by
      have := hbound (r x t) t
      change δ x t ≤ D at this
      have := hpos x t
      omega⟩
    have hg : Function.Injective g := by
      intro t s e
      have he := congrArg Fin.val e
      change δ x t - 1 = δ x s - 1 at he
      exact hδ x (by have := hpos x t; have := hpos x s; omega)
    obtain ⟨t, ht⟩ := ((Fintype.bijective_iff_injective_and_card g).2 ⟨hg, rfl⟩).2 ⟨0, by omega⟩
    have he := congrArg Fin.val ht
    change δ x t - 1 = 0 at he
    exact ⟨t, by have := hpos x t; omega⟩
  let pick (x : colors) := Classical.choose (hone x)
  have hmem (x : colors) : (r x (pick x), col (pick x)) ∈ ({v₀, v₁} : Finset _) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      hboundary (r x (pick x)) (pick x) (Classical.choose_spec (hone x))
  let g (x : colors) : {v // v ∈ ({v₀, v₁} : Finset (Fin m × Fin n))} :=
    ⟨(r x (pick x), col (pick x)), hmem x⟩
  have hg : Function.Injective g := by
    intro x y e
    apply Subtype.ext
    exact (hr x (pick x)).symm.trans ((congrArg (fun v => c v.val) e).trans (hr y (pick y)))
  have h := Fintype.card_le_of_injective g hg
  rw [hcard, Fintype.card_coe] at h
  have := Finset.card_insert_le v₀ ({v₁} : Finset _)
  rw [Finset.card_singleton] at this
  omega

#print axioms clique_lower
#print axioms bounded_run_impossible

end Locating321730
```

### `LocatingRuns.lean`

```lean
import LocatingLowerCore

open SimpleGraph

namespace Locating321730

variable {m n : ℕ}

def chain (cycle : Bool) (n : ℕ) : SimpleGraph (Fin n) :=
  if cycle then cycleGraph n else pathGraph n

theorem chain_preconnected (cycle : Bool) (n : ℕ) : (chain cycle n).Preconnected := by
  cases cycle
  · exact pathGraph_preconnected n
  · exact cycleGraph_preconnected

theorem chain_adj (cycle : Bool) (hn : 2 ≤ n) (a b : Fin n) :
    (chain cycle n).Adj a b ↔ gap a b = 1 ∨ (cycle = true ∧ gap a b + 1 = n) := by
  cases cycle
  · simpa [chain] using path_adj_iff_gap a b
  · simpa [chain] using cycle_adj_iff_gap hn a b

theorem chain_dist (cycle : Bool) (hn : 2 ≤ n) (a b : Fin n) :
    (chain cycle n).dist a b = if cycle then cycleGap a b else gap a b := by
  cases cycle
  · exact path_dist a b
  · exact cycle_dist hn a b

theorem maximal_interval (P : ℕ → Prop) {j n : ℕ} (hj : j + 1 < n)
    (h₀ : P j) (h₁ : P (j + 1)) :
    ∃ a b, a ≤ j ∧ j + 1 < b ∧ b ≤ n ∧
      (∀ t, a ≤ t → t < b → P t) ∧ (a = 0 ∨ ¬P (a - 1)) ∧ (b = n ∨ ¬P b) := by
  classical
  have hex : ∃ b, j + 1 < b ∧ (b = n ∨ ¬P b) := ⟨n, hj, Or.inl rfl⟩
  let b := Nat.find hex
  have hb := Nat.find_spec hex
  have hbn : b ≤ n := Nat.find_min' hex ⟨hj, Or.inl rfl⟩
  have haex : ∃ a, a ≤ j ∧ ∀ t, a ≤ t → t < b → P t := by
    refine ⟨j, le_rfl, ?_⟩
    intro t ht htb
    by_cases h : j + 1 < t
    · by_contra hp
      exact (Nat.find_min hex htb) ⟨h, Or.inr hp⟩
    · have : t = j ∨ t = j + 1 := by omega
      rcases this with rfl | rfl <;> assumption
  let a := Nat.find haex
  have ha := Nat.find_spec haex
  refine ⟨a, b, ha.1, hb.1, hbn, ha.2, ?_, hb.2⟩
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  · right
    intro hprev
    apply Nat.find_min haex (show a - 1 < a by omega)
    refine ⟨by omega, fun t ht htb => ?_⟩
    by_cases h : t = a - 1
    · rwa [h]
    · exact ha.2 t (by omega) htb

private theorem bounded_interval_impossible (cycle : Bool) (hm : 3 ≤ m) (hn : 2 ≤ n)
    {c : Fin m × Fin n → Fin (m + 1)} (hc : IsLocating (Grid m (chain cycle n)) c)
    {z : Fin (m + 1)} {a b : ℕ} (ha : 0 < a) (hab : a + 2 ≤ b) (hb : b ≤ n)
    (hmiss : ∀ j : Fin n, a ≤ j.val → j.val < b → ¬ Present c z j)
    (hl : Present c z ⟨a - 1, by omega⟩)
    (hr : Present c z ⟨b % n, Nat.mod_lt _ (by omega)⟩)
    (hwrap : b = n → cycle = true) : False := by
  let lo : Fin n := ⟨a - 1, by omega⟩
  let hi : Fin n := ⟨b % n, Nat.mod_lt _ (by omega)⟩
  obtain ⟨r₀, hr₀⟩ := hl
  obtain ⟨r₁, hr₁⟩ := hr
  change c (r₀, lo) = z at hr₀
  change c (r₁, hi) = z at hr₁
  let col (t : Fin (b - a)) : Fin n := ⟨a + t.val, by have := t.isLt; omega⟩
  have hcol : Function.Injective col := by
    intro t s h
    apply Fin.ext
    have := congrArg Fin.val h
    change a + t.val = a + s.val at this
    omega
  have hc0 (t : Fin (b - a)) : (col t).val = a + t.val := rfl
  have hlo : lo.val = a - 1 := rfl
  have hhi : hi.val = if b = n then 0 else b := by
    change b % n = _
    split
    · simp_all
    · exact Nat.mod_eq_of_lt (by omega)
  let v₀ : Fin m × Fin n := (r₀, ⟨a, by omega⟩)
  let v₁ : Fin m × Fin n := (r₁, ⟨b - 1, by omega⟩)
  have hH := chain_preconnected cycle n
  refine bounded_run_impossible hH hc hm (show 2 ≤ b - a by omega) col hcol
    (fun t => hmiss (col t) (by rw [hc0]; omega) (by rw [hc0]; have := t.isLt; omega))
    ?_ v₀ v₁ ?_
  · intro i t
    have h₀ := colorDist_le (G := Grid m (chain cycle n)) (v := (i, col t)) hr₀
    have h₁ := colorDist_le (G := Grid m (chain cycle n)) (v := (i, col t)) hr₁
    rw [product_dist hH, chain_dist cycle hn] at h₀ h₁
    dsimp only [Prod.fst, Prod.snd] at h₀ h₁
    have ht := t.isLt
    have h₀' : (chain cycle n).dist (col t) lo ≤ t.val + 1 := by
      rw [chain_dist cycle hn]
      have hg : gap (col t) lo = t.val + 1 := by unfold gap; rw [hc0, hlo]; omega
      cases cycle <;> simp [cycleGap, hg]
    have h₁' : (chain cycle n).dist (col t) hi ≤ b - a - t.val := by
      rw [chain_dist cycle hn]
      by_cases he : b = n
      · have hg : gap (col t) hi = a + t.val := by unfold gap; rw [hc0, hhi]; simp only [he, ite_true]; omega
        rw [hwrap he]
        change min (gap (col t) hi) (n - gap (col t) hi) ≤ _
        rw [hg]
        omega
      · have hg : gap (col t) hi = b - a - t.val := by
          unfold gap
          rw [hc0, hhi]; simp only [he, ite_false]
          omega
        cases cycle <;> simp [cycleGap, hg]
    rw [← chain_dist cycle hn] at h₀ h₁
    split at h₀ <;> split at h₁ <;> omega
  · intro i t hd
    have ht := t.isLt
    have hja : a ≤ (col t).val := by rw [hc0]; omega
    have hjb : (col t).val < b := by rw [hc0]; omega
    have hne : c (i, col t) ≠ z := fun h => hmiss _ hja hjb ⟨i, h⟩
    obtain ⟨⟨r, j⟩, hz, had⟩ :=
      (colorDist_eq_one_iff (preconnected_top.boxProd hH) hc.2.1 hne).1 hd
    rcases boxProd_adj.mp had with ⟨_, hj⟩ | ⟨hj, hir⟩
    · change col t = j at hj
      exact (hmiss _ hja hjb ⟨r, hj.symm ▸ hz⟩).elim
    change i = r at hir
    change (chain cycle n).Adj (col t) j at hj
    subst r
    have hout : j.val < a ∨ b ≤ j.val := by
      by_contra! h
      exact hmiss j h.1 h.2 ⟨i, hz⟩
    rw [chain_adj cycle hn] at hj
    have hjn := j.isLt
    have hcases : ((col t).val = a ∧ j = lo) ∨ ((col t).val = b - 1 ∧ j = hi) := by
      simp only [Fin.ext_iff, hlo, hhi]
      unfold gap at hj
      split <;> omega
    rcases hcases with ⟨ht, rfl⟩ | ⟨ht, rfl⟩
    · exact Or.inl (Prod.ext (column_injective hc.1 lo (hz.trans hr₀.symm)) (Fin.ext ht))
    · exact Or.inr (Prod.ext (column_injective hc.1 hi (hz.trans hr₁.symm)) (Fin.ext ht))

private theorem one_sided_path_impossible (hn : 2 ≤ n)
    {c : Fin m × Fin n → Fin (m + 1)} (hc : IsLocating (KP m n) c)
    {z : Fin (m + 1)} (left : Bool) {p : Fin n}
    (hRoom : if left then p.val + 2 < n else 2 ≤ p.val)
    (hp : Present c z p)
    (hNo : ∀ j : Fin n, (if left then p.val < j.val else j.val < p.val) → ¬Present c z j) :
    False := by
  let hH := pathGraph_preconnected n
  obtain ⟨r, hr⟩ := hp
  let j : Fin n := ⟨if left then n - 1 else 0, by split <;> omega⟩
  let j' : Fin n := ⟨if left then n - 2 else 1, by split <;> omega⟩
  have hj : j.val = if left then n - 1 else 0 := rfl
  have hj' : j'.val = if left then n - 2 else 1 := rfl
  have h₀ : ¬ Present c z j := hNo j (by rw [hj]; cases left <;> simp_all <;> omega)
  have h₁ : ¬ Present c z j' := hNo j' (by rw [hj']; cases left <;> simp_all <;> omega)
  have hx : c (r, j) ≠ z := fun e => h₀ ⟨r, e⟩
  obtain ⟨r', hr'⟩ := present_of_ne_missing hc.1 h₁ hx
  have had : (pathGraph n).Adj j j' := by
    rw [pathGraph_adj, hj, hj']
    cases left
    · simp
    · simp
      omega
  have hrr' : r' ≠ r := by
    rintro rfl
    exact hc.1 (r', j) (r', j') (Or.inr ⟨had, rfl⟩) hr'.symm
  have exactDist (i : Fin m) (t : Fin n)
      (ht : if left then p.val < t.val else t.val < p.val) :
      colorDist (KP m n) c (i, t) z = (if i = r then 0 else 1) + gap t p := by
    apply le_antisymm
    · have h := colorDist_le (G := KP m n) (v := (i, t)) hr
      rwa [KP, product_dist hH, path_dist] at h
    · obtain ⟨⟨s, q⟩, hsq, hdist⟩ :=
        colorDist_attained (G := KP m n) (v := (i, t)) (hc.2.1 z)
      rw [← hdist, KP, product_dist hH, path_dist]
      by_cases he : q = p
      · subst q
        rw [column_injective hc.1 p (hsq.trans hr.symm)]
      · have hq : ¬(if left then p.val < q.val else q.val < p.val) := fun h => hNo q h ⟨s, hsq⟩
        have hqp := mt Fin.ext he
        unfold gap
        dsimp only [Prod.fst, Prod.snd]
        cases left <;> simp at hq ht <;> split <;> split <;> omega
  have h := only_missing_coordinate hH hc h₀ h₁ hr'.symm (by
    change colorDist (KP m n) c (r, j) z = colorDist (KP m n) c (r', j') z
    rw [exactDist r j (by rw [hj]; cases left <;> simp_all <;> omega),
      exactDist r' j' (by rw [hj']; cases left <;> simp_all <;> omega)]
    simp only [hrr', ite_false, ite_true, eq_self]
    unfold gap
    rw [hj, hj']
    cases left <;> simp_all <;> omega)
  have he := congrArg (fun v : Fin m × Fin n => v.2.val) h
  change j.val = j'.val at he
  rw [hj, hj'] at he
  cases left <;> simp_all

private theorem linear_missing_distinct (cycle : Bool) (hm : 3 ≤ m) (hn : 2 ≤ n)
    {c : Fin m × Fin n → Fin (m + 1)} (hc : IsLocating (Grid m (chain cycle n)) c)
    {z : Fin (m + 1)} (hcut : cycle = true → Present c z ⟨0, by omega⟩)
    {j j' : Fin n} (hjj : j.val + 1 = j'.val) (h₀ : ¬Present c z j)
    (h₁ : ¬Present c z j') : False := by
  classical
  let P (t : ℕ) := ∀ h : t < n, ¬Present c z ⟨t, h⟩
  obtain ⟨a, b, haj, hjb, hbn, hP, ha, hb⟩ :=
    maximal_interval P (show j.val + 1 < n by rw [hjj]; exact j'.isLt)
      (fun _ => h₀) (fun _ => by simpa only [hjj] using h₁)
  have hmiss (t : Fin n) (hta : a ≤ t.val) (htb : t.val < b) : ¬Present c z t :=
    hP t.val hta htb t.isLt
  have atPresent (t : ℕ) (ht : t < n) (hp : ¬ P t) : Present c z ⟨t, ht⟩ := by
    by_contra h
    exact hp fun _ => h
  rcases ha with rfl | ha
  · have hfalse : cycle = false := by
      cases cycle
      · rfl
      · exact (hmiss ⟨0, by omega⟩ (by simp) (show 0 < b by omega) (hcut rfl)).elim
    subst cycle
    rcases hb with rfl | hb
    · obtain ⟨⟨r, t⟩, hr⟩ := hc.2.1 z
      exact hmiss t (by simp) t.isLt ⟨r, hr⟩
    · have hlt : b < n := by
        by_contra! h
        apply hb
        intro hlt
        exact (Nat.not_lt_of_ge h hlt).elim
      exact one_sided_path_impossible hn hc false (p := ⟨b, hlt⟩)
        (by change 2 ≤ b; omega) (atPresent b hlt hb)
        (fun t ht => hmiss t (Nat.zero_le _) ht)
  · have ha0 : 0 < a := by
      by_contra! h
      have he : a = 0 := by omega
      apply ha
      simpa [he] using hP a le_rfl (by omega)
    have hap : a - 1 < n := (Nat.sub_le a 1).trans_lt (haj.trans_lt j.isLt)
    have hlo : Present c z ⟨a - 1, hap⟩ := atPresent (a - 1) hap ha
    by_cases hbn' : b = n
    · cases cycle
      · exact one_sided_path_impossible hn hc true (p := ⟨a - 1, hap⟩)
          (by
            change a - 1 + 2 < n
            have h : a + 1 < n := Nat.lt_of_le_of_lt (Nat.succ_le_succ haj) (hbn' ▸ hjb)
            exact (show a - 1 + 2 ≤ a + 1 by omega).trans_lt h) hlo
          (fun t ht => hmiss t (by
            change a - 1 < t.val at ht
            exact (Nat.succ_pred_eq_of_pos ha0) ▸ Nat.succ_le_of_lt ht) (hbn' ▸ t.isLt))
      · refine bounded_interval_impossible true hm hn hc ha0 (by omega) hbn hmiss hlo ?_ (fun _ => rfl)
        simpa [hbn'] using hcut rfl
    · have hlt : b < n := Nat.lt_of_le_of_ne hbn hbn'
      have hp := atPresent b hlt (hb.resolve_left hbn')
      refine bounded_interval_impossible cycle hm hn hc ha0 (by omega) hbn hmiss hlo ?_
        (fun h => (hbn' h).elim)
      have he : (⟨b % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = ⟨b, hlt⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hlt)
      rwa [he]

private theorem dist_le_of_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hG : G.Preconnected) (u v : V) : H.dist (f u) (f v) ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := (hG u v).exists_walk_length_eq_dist
  simpa [hp] using H.dist_le (p.map f)

private theorem dist_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : G.Preconnected) (hH : H.Preconnected) (v w : V) :
    H.dist (e v) (e w) = G.dist v w := by
  exact le_antisymm (dist_le_of_hom e.toHom hG v w) (by
    simpa using dist_le_of_hom e.symm.toHom hH (e v) (e w))

private theorem colorDist_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {k : ℕ} (e : G ≃g H) (hG : G.Preconnected) (hH : H.Preconnected)
    (c : W → Fin k) (v : V) (x : Fin k) :
    colorDist G (c ∘ e) v x = colorDist H c (e v) x := by
  unfold colorDist
  congr 1
  ext d
  constructor
  · rintro ⟨w, hw, hd⟩
    exact ⟨e w, hw, (dist_iso e hG hH v w).trans hd⟩
  · rintro ⟨w, hw, hd⟩
    obtain ⟨u, rfl⟩ := e.surjective w
    exact ⟨u, hw, (dist_iso e hG hH v u).symm.trans hd⟩

private def rotateGrid [NeZero n] (a : Fin n) : KC m n ≃g KC m n where
  toEquiv := Equiv.prodCongr (Equiv.refl _) (Equiv.addRight a)
  map_rel_iff' := by
    intro u v
    simp [KC, boxProd_adj, cycleGraph_adj', add_sub_add_right_eq_sub]

theorem adjacent_missing_distinct (cycle : Bool) (hm : 3 ≤ m) (hn : 2 ≤ n)
    {c : Fin m × Fin n → Fin (m + 1)} (hc : IsLocating (Grid m (chain cycle n)) c)
    {z : Fin (m + 1)} {j j' : Fin n} (hadj : (chain cycle n).Adj j j')
    (h₀ : ¬Present c z j) (h₁ : ¬Present c z j') : False := by
  cases cycle with
  | false =>
    change (pathGraph n).Adj j j' at hadj
    rcases pathGraph_adj.mp hadj with h | h
    · exact linear_missing_distinct false hm hn hc (by simp) h h₀ h₁
    · exact linear_missing_distinct false hm hn hc (by simp) h h₁ h₀
  | true =>
    let : NeZero n := ⟨by omega⟩
    obtain ⟨⟨r, a⟩, hr⟩ := hc.2.1 z
    let e : KC m n ≃g KC m n := rotateGrid a
    let c' := c ∘ e
    have hG : (KC m n).Preconnected := preconnected_top.boxProd cycleGraph_preconnected
    have hc' : IsLocating (KC m n) c' := by
      refine ⟨fun u v h => hc.1 _ _ (e.toHom.map_adj h), hc.2.1.comp e.surjective, ?_⟩
      intro u v h
      apply e.injective
      apply hc.2.2
      funext x
      exact (colorDist_iso e hG hG c u x).symm.trans
        ((congrFun h x).trans (colorDist_iso e hG hG c v x))
    have hcut : Present c' z ⟨0, by omega⟩ := ⟨r, by
      change c (r, (⟨0, by omega⟩ : Fin n) + a) = z
      have he : (⟨0, by omega⟩ : Fin n) = 0 := rfl
      rwa [he, zero_add]⟩
    have hMiss (t : Fin n) (ht : ¬Present c z t) : ¬Present c' z (t - a) := by
      rintro ⟨i, hi⟩
      change c (i, t - a + a) = z at hi
      rw [sub_add_cancel] at hi
      exact ht ⟨i, hi⟩
    have hAdj : (cycleGraph n).Adj (j - a) (j' - a) := by
      change (cycleGraph n).Adj j j' at hadj
      simpa only [cycleGraph_adj', sub_sub_sub_cancel_right] using hadj
    have hz (t : Fin n) (ht : ¬Present c' z t) : t.val ≠ 0 := by
      intro he
      have hEq : t = (⟨0, by omega⟩ : Fin n) := Fin.ext he
      exact ht (hEq.symm ▸ hcut)
    have hf₀ := hMiss j h₀
    have hf₁ := hMiss j' h₁
    have hpos₀ := hz _ hf₀
    have hpos₁ := hz _ hf₁
    rw [cycle_adj_iff_gap hn] at hAdj
    unfold gap at hAdj
    have hlt₀ := (j - a).isLt
    have hlt₁ := (j' - a).isLt
    have hcases : (j - a).val + 1 = (j' - a).val ∨ (j' - a).val + 1 = (j - a).val := by
      omega
    rcases hcases with h | h
    · exact linear_missing_distinct true hm hn hc' (fun _ => hcut) h hf₀ hf₁
    · exact linear_missing_distinct true hm hn hc' (fun _ => hcut) h hf₁ hf₀

theorem many_columns_lower (cycle : Bool) (hm : 3 ≤ m) (hn : 2 ≤ n) {k : ℕ}
    (hlarge : m + 2 ≤ n) {c : Fin m × Fin n → Fin k}
    (hc : IsLocating (Grid m (chain cycle n)) c) : m + 2 ≤ k := by
  have hH := chain_preconnected cycle n
  have hClique := clique_lower hH (show 0 < m by omega) hn hc
  by_contra! h
  have hk : k = m + 1 := by omega
  subst k
  have hcolor (j : Fin n) : ∃ i : Fin m, Colorful (Grid m (chain cycle n)) c (i, j) := by
    obtain ⟨z, hz⟩ := missing_exists hc.1 j
    obtain ⟨j', hj'⟩ : ∃ j', (chain cycle n).Adj j j' := by
      by_cases hj : j.val + 1 < n
      · exact ⟨⟨j.val + 1, hj⟩, (chain_adj cycle hn _ _).2 (Or.inl (by simp [gap]))⟩
      · refine ⟨⟨j.val - 1, by have := j.isLt; omega⟩, (chain_adj cycle hn _ _).2 (Or.inl ?_)⟩
        unfold gap
        have := j.isLt
        dsimp
        omega
    have hp : Present c z j' := by
      by_contra hnz
      exact adjacent_missing_distinct cycle hm hn hc hj' hz hnz
    obtain ⟨i, hi⟩ := hp
    refine ⟨i, fun x => ?_⟩
    by_cases hx : x = z
    · subst x
      have hne : c (i, j) ≠ z := fun e => hz ⟨i, e⟩
      have hd := (colorDist_eq_one_iff (preconnected_top.boxProd hH) hc.2.1 hne).2
        ⟨(i, j'), hi, Or.inr ⟨hj', rfl⟩⟩
      simp [hd, hne]
    · exact column_dist hH hc.2.1 (present_of_ne_missing hc.1 hz hx)
  choose row hrow using hcolor
  have hInj : Function.Injective (fun j => c (row j, j)) := fun j j' h =>
    congrArg Prod.snd (colorful_injective hc (hrow j) (hrow j') h)
  have hn' : n ≤ m + 1 := by simpa using Fintype.card_le_of_injective _ hInj
  omega

#print axioms adjacent_missing_distinct
#print axioms many_columns_lower

end Locating321730
```

### `LocatingHall.lean`

```lean
import LocatingRuns
import Mathlib.Combinatorics.Hall.Basic

open SimpleGraph

namespace Locating321730

variable {R C J : Type*} [DecidableEq R] [DecidableEq C] [DecidableEq J]

/-- Match the free rows to available colours when each of the two adjoining columns
forbids at most one colour per row and at most one row per colour. -/
theorem two_column_matching (rows : Finset R) (colors : Finset C)
    (hcard : rows.card = colors.card) (hfour : 4 ≤ colors.card)
    (p q : R → Option C)
    (hp : ∀ i j x, p i = some x → p j = some x → i = j)
    (hq : ∀ i j x, q i = some x → q j = some x → i = j) :
    ∃ f : rows → C, Function.Injective f ∧
      ∀ i, f i ∈ colors ∧ p i ≠ some (f i) ∧ q i ≠ some (f i) := by
  let allowed (i : rows) := colors.filter fun x => p i ≠ some x ∧ q i ≠ some x
  have hmem (i : rows) (x : C) :
      x ∈ allowed i ↔ x ∈ colors ∧ p i ≠ some x ∧ q i ≠ some x := Finset.mem_filter
  have hall : ∀ S : Finset rows, S.card ≤ (S.biUnion allowed).card := by
    intro S
    classical
    by_cases hempty : S = ∅
    · simp [hempty]
    by_cases hsmall : S.card ≤ colors.card - 2
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      let ban (t : Option C) : Finset C := t.elim ∅ fun x => {x}
      have hb (t : Option C) (x : C) : x ∈ ban t ↔ t = some x := by
        cases t <;> simp [ban, eq_comm]
      have hbc (t : Option C) : (ban t).card ≤ 1 := by cases t <;> simp [ban]
      have hle : (ban (p i) ∪ ban (q i)).card ≤ 2 :=
        (Finset.card_union_le _ _).trans (by have := hbc (p i); have := hbc (q i); omega)
      have hsub : colors \ (ban (p i) ∪ ban (q i)) ⊆ S.biUnion allowed := by
        intro x hx
        rw [Finset.mem_sdiff, Finset.mem_union, hb, hb, not_or] at hx
        exact Finset.mem_biUnion.mpr ⟨i, hi, (hmem i x).mpr hx⟩
      have h₀ := Finset.le_card_sdiff (ban (p i) ∪ ban (q i)) colors
      have h₁ := Finset.card_le_card hsub
      omega
    · have hlarge : 3 ≤ S.card := by omega
      have hsub : colors ⊆ S.biUnion allowed := by
        intro x hx
        by_contra hnone
        let bad₀ := S.filter fun (i : rows) => p i = some x
        let bad₁ := S.filter fun (i : rows) => q i = some x
        have h₀ : bad₀.card ≤ 1 := Finset.card_le_one.mpr fun i hi j hj =>
          Subtype.ext (hp i j x (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
        have h₁ : bad₁.card ≤ 1 := Finset.card_le_one.mpr fun i hi j hj =>
          Subtype.ext (hq i j x (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
        have hh : S ⊆ bad₀ ∪ bad₁ := by
          intro i hi
          have hb : ¬ (p i ≠ some x ∧ q i ≠ some x) := fun hpq =>
            hnone (Finset.mem_biUnion.mpr ⟨i, hi, (hmem i x).mpr ⟨hx, hpq⟩⟩)
          simp only [Finset.mem_union, bad₀, bad₁, Finset.mem_filter, hi, true_and]
          tauto
        have h := (Finset.card_le_card hh).trans (Finset.card_union_le _ _)
        omega
      have hs : S.card ≤ rows.card := by
        simpa [Fintype.card_coe] using (Finset.card_le_univ S)
      exact (hs.trans_eq hcard).trans (Finset.card_le_card hsub)
  simpa only [hmem] using (Finset.all_card_le_biUnion_card_iff_exists_injective allowed).mp hall

structure PartialColoring (next : J → J) (missing : J → C)
    (p : R → J → Option C) : Prop where
  column : ∀ j i i' x, p i j = some x → p i' j = some x → i = i'
  excludes : ∀ i j, p i j ≠ some (missing j)
  edge : ∀ i j x, p i j = some x → p i (next j) ≠ some x

theorem fill_column (next : J ≃ J) (missing : J → C) (base : R → J → Option C)
    (hb : PartialColoring next missing base)
    (j : J) (hnext : next j ≠ j)
    (rows : Finset R) (colors : Finset C) (hcard : rows.card = colors.card)
    (hfour : 4 ≤ colors.card)
    (hr : ∀ i, i ∈ rows ↔ base i j = none)
    (hcolor : ∀ x ∈ colors, x ≠ missing j ∧ ∀ i, base i j ≠ some x) :
    ∃ filled : R → J → Option C, PartialColoring next missing filled ∧
      (∀ i k x, base i k = some x → filled i k = some x) ∧
      (∀ i k, k ≠ j → filled i k = base i k) ∧
      (∀ i, ∃ x, filled i j = some x) := by
  obtain ⟨f, hfi, hf⟩ := two_column_matching rows colors hcard hfour
    (fun i => base i (next.symm j)) (fun i => base i (next j))
    (hb.column _) (hb.column _)
  let fill (i : R) (k : J) : Option C :=
    if e : k = j ∧ i ∈ rows then some (f ⟨i, e.2⟩) else base i k
  have hset (i : R) (hi : i ∈ rows) : fill i j = some (f ⟨i, hi⟩) := by simp [fill, hi]
  have hunset (i : R) (k : J) (h : k ≠ j ∨ i ∉ rows) : fill i k = base i k := by
    rcases h with h | h <;> simp [fill, h]
  have hbefore (i : R) (k : J) (x : C) (hx : base i k = some x) :
      fill i k = some x := by
    by_cases e : k = j
    · subst k
      have hi : i ∉ rows := fun h => by rw [(hr i).mp h] at hx; contradiction
      exact (hunset i j (Or.inr hi)).trans hx
    · exact (hunset i k (Or.inl e)).trans hx
  refine ⟨fill, ⟨?_, ?_, ?_⟩, hbefore, fun i k h => hunset i k (.inl h), ?_⟩
  · intro k i i' x h₀ h₁
    by_cases e : k = j
    · subst k
      by_cases hi : i ∈ rows <;> by_cases hi' : i' ∈ rows
      · rw [hset i hi] at h₀
        rw [hset i' hi'] at h₁
        exact congrArg Subtype.val (hfi (Option.some.inj (h₀.trans h₁.symm)))
      · rw [hset i hi] at h₀
        rw [hunset i' j (.inr hi')] at h₁
        exact ((hcolor _ (hf ⟨i, hi⟩).1).2 i' (h₁.trans h₀.symm)).elim
      · rw [hunset i j (.inr hi)] at h₀
        rw [hset i' hi'] at h₁
        exact ((hcolor _ (hf ⟨i', hi'⟩).1).2 i (h₀.trans h₁.symm)).elim
      · rw [hunset i j (.inr hi)] at h₀
        rw [hunset i' j (.inr hi')] at h₁
        exact hb.column j i i' x h₀ h₁
    · rw [hunset i k (.inl e)] at h₀
      rw [hunset i' k (.inl e)] at h₁
      exact hb.column k i i' x h₀ h₁
  · intro i k h
    by_cases e : k = j
    · subst k
      by_cases hi : i ∈ rows
      · rw [hset i hi] at h
        exact (hcolor _ (hf ⟨i, hi⟩).1).1 (Option.some.inj h)
      · exact hb.excludes i j ((hunset i j (.inr hi)).symm.trans h)
    · exact hb.excludes i k ((hunset i k (.inl e)).symm.trans h)
  · intro i k x h₀ h₁
    by_cases hi : i ∈ rows
    · by_cases e : k = j
      · subst k
        rw [hset i hi] at h₀
        rw [hunset i (next j) (.inl hnext)] at h₁
        exact (hf ⟨i, hi⟩).2.2 (h₁.trans h₀.symm)
      · by_cases e' : next k = j
        · have hk : k = next.symm j := by rw [← e', Equiv.symm_apply_apply]
          rw [hunset i k (.inl e), hk] at h₀
          rw [e', hset i hi] at h₁
          exact (hf ⟨i, hi⟩).2.1 (h₀.trans h₁.symm)
        · exact hb.edge i k x ((hunset i k (.inl e)).symm.trans h₀)
            ((hunset i (next k) (.inl e')).symm.trans h₁)
    · exact hb.edge i k x ((hunset i k (.inr hi)).symm.trans h₀)
        ((hunset i (next k) (.inr hi)).symm.trans h₁)
  · intro i
    by_cases hi : i ∈ rows
    · exact ⟨_, hset i hi⟩
    · have hn : base i j ≠ none := fun h => hi ((hr i).mpr h)
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hn
      exact ⟨x, hbefore i j x hx⟩

/-- Fill the columns in numerical order, preserving every prescribed cell. -/
theorem complete_columns {n : ℕ} (next : Fin n ≃ Fin n) (missing : Fin n → C)
    (base : R → Fin n → Option C) (hb : PartialColoring next missing base)
    (hnext : ∀ j, next j ≠ j)
    (rows : Fin n → Finset R) (colors : Fin n → Finset C)
    (hcard : ∀ j, (rows j).card = (colors j).card) (hfour : ∀ j, 4 ≤ (colors j).card)
    (hr : ∀ i j, i ∈ rows j ↔ base i j = none)
    (hcolor : ∀ j x, x ∈ colors j → x ≠ missing j ∧ ∀ i, base i j ≠ some x) :
    ∃ f : R → Fin n → C, PartialColoring next missing (fun i j => some (f i j)) ∧
      ∀ i j x, base i j = some x → f i j = x := by
  classical
  have stage (t : ℕ) : t ≤ n → ∃ p : R → Fin n → Option C,
      PartialColoring next missing p ∧
      (∀ i j x, base i j = some x → p i j = some x) ∧
      (∀ i j, t ≤ j.val → p i j = base i j) ∧
      ∀ i j, j.val < t → ∃ x, p i j = some x := by
    induction t with
    | zero =>
      intro _
      exact ⟨base, hb, fun _ _ _ h => h, fun _ _ _ => rfl, fun _ _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ t ih =>
      intro ht
      let j : Fin n := ⟨t, by omega⟩
      obtain ⟨p, hp, hbefore, hafter, hfull⟩ := ih (by omega)
      have he (i : R) : p i j = base i j := hafter i j le_rfl
      obtain ⟨q, hq, hkeep, hsame, hnew⟩ :=
        fill_column next missing p hp j (hnext j) (rows j) (colors j) (hcard j) (hfour j)
          (fun i => by rw [he i]; exact hr i j)
          (fun x hx => ⟨(hcolor j x hx).1, fun i => by rw [he i]; exact (hcolor j x hx).2 i⟩)
      refine ⟨q, hq, fun i k x h => hkeep i k x (hbefore i k x h), ?_, ?_⟩
      · intro i k hk
        have hne : k ≠ j := fun e => by subst k; exact Nat.not_succ_le_self _ hk
        exact (hsame i k hne).trans (hafter i k (by omega))
      · intro i k hk
        by_cases h : k = j
        · subst k
          exact hnew i
        · have hval : k.val ≠ t := fun e => h (Fin.ext e)
          obtain ⟨x, hx⟩ := hfull i k (by omega)
          exact ⟨x, hkeep i k x hx⟩
  obtain ⟨p, hp, hb', _, hc⟩ := stage n le_rfl
  let f (i : R) (j : Fin n) : C := Classical.choose (hc i j j.isLt)
  have he (i : R) (j : Fin n) : p i j = some (f i j) := Classical.choose_spec (hc i j j.isLt)
  have eq : p = fun i j => some (f i j) := funext fun i => funext fun j => he i j
  exact ⟨f, eq ▸ hp, fun i j x h => Option.some.inj ((he i j).symm.trans (hb' i j x h))⟩

end Locating321730
```

### `LocatingSmall.lean`

```lean
import LocatingHall

open SimpleGraph

namespace Locating321730

variable {m n : ℕ} [NeZero n]

def nextCol (n : ℕ) [NeZero n] : Fin n ≃ Fin n := Equiv.addRight 1

@[simp] theorem nextCol_apply (a : Fin n) : nextCol n a = a + 1 := rfl

theorem cycle_adj_iff_next (hn : 2 ≤ n) (a b : Fin n) :
    (cycleGraph n).Adj a b ↔ b = nextCol n a ∨ a = nextCol n b := by
  have h (x : Fin n) : x.val = 1 ↔ x = 1 := by
    have hv : (1 : Fin n).val = 1 := by
      change 1 % n = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.ext_iff, hv]
  rw [cycleGraph_adj', h, h, nextCol_apply, nextCol_apply, sub_eq_iff_eq_add, sub_eq_iff_eq_add]
  rw [add_comm (1 : Fin n) a, add_comm (1 : Fin n) b]
  exact or_comm

private theorem fin_one_val (hn : 4 ≤ n) : (1 : Fin n).val = 1 := by
  change 1 % n = 1
  exact Nat.mod_eq_of_lt (by omega)

private theorem fin_two_val (hn : 4 ≤ n) : (2 : Fin n).val = 2 := by
  change 2 % n = 2
  exact Nat.mod_eq_of_lt (by omega)

private theorem fin_three_val (hn : 4 ≤ n) : (3 : Fin n).val = 3 := by
  change 3 % n = 3
  exact Nat.mod_eq_of_lt (by omega)

private theorem add_two (a : Fin n) : a + 1 + 1 = a + 2 := by
  rw [add_assoc, show (1 : Fin n) + 1 = 2 by
    apply Fin.ext
    change (1 % n + 1 % n) % n = 2 % n
    exact (Nat.add_mod 1 1 n).symm]

private theorem add_three (a : Fin n) : a + 2 + 1 = a + 3 := by
  rw [add_assoc, show (2 : Fin n) + 1 = 3 by
    apply Fin.ext
    change (2 % n + 1 % n) % n = 3 % n
    exact (Nat.add_mod 2 1 n).symm]

private theorem adjacent_offset_ne (hn : 4 ≤ n) (a : Fin n) :
    a + 1 ≠ a ∧ a + 2 ≠ a ∧ a + 3 ≠ a := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h' : (1 : Fin n) = 0 := add_left_cancel (h.trans (add_zero a).symm)
    have h'' := congrArg Fin.val h'
    rw [fin_one_val hn] at h''
    exact Nat.one_ne_zero h''
  · intro h
    have h' : (2 : Fin n) = 0 := add_left_cancel (h.trans (add_zero a).symm)
    have h'' := congrArg Fin.val h'
    rw [fin_two_val hn] at h''
    exact Nat.noConfusion h''
  · intro h
    have h' : (3 : Fin n) = 0 := add_left_cancel (h.trans (add_zero a).symm)
    have h'' := congrArg Fin.val h'
    rw [fin_three_val hn] at h''
    exact Nat.noConfusion h''

def shortLabel (hnm : n ≤ m + 1) (a : Fin n) : Fin (m + 1) :=
  ⟨a.val, a.isLt.trans_le hnm⟩

omit [NeZero n] in
theorem shortLabel_injective (hnm : n ≤ m + 1) :
    Function.Injective (shortLabel hnm) :=
  fun _ _ e => Fin.ext (congrArg (fun x : Fin (m + 1) => x.val) e)

def specialRow (hm : 7 ≤ m) (_hnm : n ≤ m + 1) (a : Fin n) : Fin m :=
  if ha : a.val < m then ⟨a.val, ha⟩ else ⟨2, by omega⟩

omit [NeZero n] in
private theorem specialRow_ne (hm : 7 ≤ m) (hnm : n ≤ m + 1) (_hn : 4 ≤ n)
    (a : Fin n) (s : Fin n) (hs : s.val = 1 ∨ s.val = 2) :
    specialRow hm hnm (a + s) ≠ specialRow hm hnm a := by
  intro h
  have hval := congrArg Fin.val h
  have ha := a.isLt
  have hab := (a + s).isLt
  have hadd := Fin.val_add_eq_ite a s
  have hr (j : Fin n) : (specialRow hm hnm j).val = if j.val < m then j.val else 2 := by
    unfold specialRow
    split <;> rfl
  rw [hr, hr] at hval
  split at hval <;> split at hval <;> split at hadd <;> omega

variable (hm : 7 ≤ m) (hnm : n ≤ m + 1)

def specialCell (i : Fin m) (a : Fin n) : Option (Fin (m + 1)) :=
  if i = specialRow hm hnm (a - 1) then some (shortLabel hnm (a - 1))
  else if i = specialRow hm hnm a then some (shortLabel hnm (a + 2))
  else if i = specialRow hm hnm (a + 1) then some (shortLabel hnm (a + 1))
  else none

variable (hn : 4 ≤ n)

include hn in
private theorem specialRow_three (a : Fin n) :
    specialRow hm hnm a ≠ specialRow hm hnm (a - 1) ∧
    specialRow hm hnm (a + 1) ≠ specialRow hm hnm a ∧
    specialRow hm hnm (a + 1) ≠ specialRow hm hnm (a - 1) := by
  refine ⟨?_, specialRow_ne hm hnm hn a 1 (Or.inl (fin_one_val hn)), ?_⟩
  · simpa only [sub_add_cancel] using specialRow_ne hm hnm hn (a - 1) 1 (Or.inl (fin_one_val hn))
  · have h := specialRow_ne hm hnm hn (a - 1) 2 (Or.inr (fin_two_val hn))
    rwa [← add_two, sub_add_cancel] at h

include hn in
private theorem special_labels (a : Fin n) :
    a - 1 ≠ a ∧ a + 1 ≠ a ∧ a + 2 ≠ a ∧
    a + 1 ≠ a - 1 ∧ a + 2 ≠ a - 1 ∧ a + 2 ≠ a + 1 := by
  have h := adjacent_offset_ne hn a
  refine ⟨?_, h.1, h.2.1, ?_, ?_, ?_⟩
  · intro he
    have hh := congrArg (· + 1) he
    rw [sub_add_cancel] at hh
    exact h.1 hh.symm
  · intro he
    have hh := congrArg (· + 1) he
    rw [add_two, sub_add_cancel] at hh
    exact h.2.1 hh
  · intro he
    have hh := congrArg (· + 1) he
    rw [add_three, sub_add_cancel] at hh
    exact h.2.2 hh
  · rw [← add_two]
    exact (adjacent_offset_ne hn (a + 1)).1

private theorem special_cases {i : Fin m} {a : Fin n} {x : Fin (m + 1)}
    (hx : specialCell hm hnm i a = some x) :
    (i = specialRow hm hnm (a - 1) ∧ x = shortLabel hnm (a - 1)) ∨
    (i = specialRow hm hnm a ∧ x = shortLabel hnm (a + 2)) ∨
    (i = specialRow hm hnm (a + 1) ∧ x = shortLabel hnm (a + 1)) := by
  unfold specialCell at hx
  split at hx
  · exact .inl ⟨by assumption, (Option.some.inj hx).symm⟩
  split at hx
  · exact .inr (.inl ⟨by assumption, (Option.some.inj hx).symm⟩)
  split at hx
  · exact .inr (.inr ⟨by assumption, (Option.some.inj hx).symm⟩)
  · contradiction

include hn in
private theorem special_mates (a : Fin n) :
    specialCell hm hnm (specialRow hm hnm (a - 1)) a = some (shortLabel hnm (a - 1)) ∧
    specialCell hm hnm (specialRow hm hnm a) a = some (shortLabel hnm (a + 2)) ∧
    specialCell hm hnm (specialRow hm hnm (a + 1)) a = some (shortLabel hnm (a + 1)) := by
  have h := specialRow_three hm hnm hn a
  simp [specialCell, h.1, h.2.1, h.2.2]

include hn in
private theorem special_proper : PartialColoring (nextCol n) (shortLabel hnm) (specialCell hm hnm) where
  column := by
    intro a i j x hi hj
    have h := special_labels hn a
    obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := h
    have hh := shortLabel_injective hnm
    rcases special_cases hm hnm hi with ⟨rfl, hxi⟩ | ⟨rfl, hxi⟩ | ⟨rfl, hxi⟩ <;>
      rcases special_cases hm hnm hj with ⟨rfl, hxj⟩ | ⟨rfl, hxj⟩ | ⟨rfl, hxj⟩ <;>
      first | rfl | exact (h₃ (hh (hxi.symm.trans hxj)).symm).elim |
        exact (h₃ (hh (hxi.symm.trans hxj))).elim |
        exact (h₄ (hh (hxi.symm.trans hxj)).symm).elim |
        exact (h₄ (hh (hxi.symm.trans hxj))).elim |
        exact (h₅ (hh (hxi.symm.trans hxj)).symm).elim |
        exact (h₅ (hh (hxi.symm.trans hxj))).elim
  excludes := by
    intro i a h
    obtain ⟨h₀, h₁, h₂, _, _, _⟩ := special_labels hn a
    rcases special_cases hm hnm h with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩
    · exact h₀ (shortLabel_injective hnm hx.symm)
    · exact h₂ (shortLabel_injective hnm hx.symm)
    · exact h₁ (shortLabel_injective hnm hx.symm)
  edge := by
    intro i a x h₀ h₁
    rw [nextCol_apply] at h₁
    have rne₀ := specialRow_three hm hnm hn a
    have rne₁ := specialRow_three hm hnm hn (a + 1)
    rw [add_sub_cancel_right, add_two] at rne₁
    have hleft := special_cases hm hnm h₀
    have hright := special_cases hm hnm h₁
    rw [add_sub_cancel_right, add_two] at hright
    have hx₁ (h : x = shortLabel hnm (a + 2)) (h' : x = shortLabel hnm a) : False :=
      (adjacent_offset_ne hn a).2.1 (shortLabel_injective hnm (h.symm.trans h'))
    have hx₂ (h : x = shortLabel hnm (a + 1)) (h' : x = shortLabel hnm (a + 1 + 2)) : False :=
      (adjacent_offset_ne hn (a + 1)).2.1 (shortLabel_injective hnm (h'.symm.trans h))
    have hx₃ (h : x = shortLabel hnm (a - 1)) (h' : x = shortLabel hnm (a + 2)) : False :=
      (special_labels hn a).2.2.2.2.1 (shortLabel_injective hnm (h'.symm.trans h))
    rcases hleft with ⟨hl, xl⟩ | ⟨hl, xl⟩ | ⟨hl, xl⟩ <;>
      rcases hright with ⟨hr, xr⟩ | ⟨hr, xr⟩ | ⟨hr, xr⟩
    · exact rne₀.1 (hr.symm.trans hl)
    · exact rne₀.2.2 (hr.symm.trans hl)
    · exact hx₃ xl xr
    · exact hx₁ xl xr
    · exact rne₀.2.1 (hr.symm.trans hl)
    · exact rne₁.2.2 (hr.symm.trans hl)
    · exact rne₀.2.1 (hl.symm.trans hr)
    · exact hx₂ xl xr
    · exact rne₁.2.1 (hr.symm.trans hl)


private def freeRows (a : Fin n) : Finset (Fin m) :=
  Finset.univ \ {specialRow hm hnm (a - 1), specialRow hm hnm a, specialRow hm hnm (a + 1)}

private def freeColors (a : Fin n) : Finset (Fin (m + 1)) :=
  Finset.univ \ {shortLabel hnm (a - 1), shortLabel hnm a,
    shortLabel hnm (a + 1), shortLabel hnm (a + 2)}

include hn in
private theorem freeRows_card (a : Fin n) : (freeRows hm hnm a).card = m - 3 := by
  obtain ⟨h₀, h₁, h₂⟩ := specialRow_three hm hnm hn a
  unfold freeRows
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hne : specialRow hm hnm (a - 1) ∉
      ({specialRow hm hnm a, specialRow hm hnm (a + 1)} : Finset _) := by
    simp [ne_comm, h₀, h₂]
  rw [Finset.card_insert_of_notMem hne, Finset.card_pair h₁.symm]
  simp

include hn in
private theorem freeColors_card (a : Fin n) : (freeColors hnm a).card = m - 3 := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := special_labels hn a
  have hi := shortLabel_injective hnm
  unfold freeColors
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hleft : shortLabel hnm (a - 1) ∉
      ({shortLabel hnm a, shortLabel hnm (a + 1), shortLabel hnm (a + 2)} : Finset _) := by
    simp [hi.eq_iff, h₀, h₃.symm, h₄.symm]
  have hmid : shortLabel hnm a ∉
      ({shortLabel hnm (a + 1), shortLabel hnm (a + 2)} : Finset _) := by
    simp [hi.eq_iff, h₁.symm, h₂.symm]
  rw [Finset.card_insert_of_notMem hleft, Finset.card_insert_of_notMem hmid,
    Finset.card_pair (fun h => h₅ (hi h).symm)]
  simp

private theorem freeRows_iff (i : Fin m) (a : Fin n) :
    i ∈ freeRows hm hnm a ↔ specialCell hm hnm i a = none := by
  simp only [freeRows, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
    Finset.mem_singleton, true_and, specialCell]
  split <;> simp_all
  split <;> simp_all

private theorem freeColors_avoid (a : Fin n) (x : Fin (m + 1)) (hx : x ∈ freeColors hnm a) :
    x ≠ shortLabel hnm a ∧ ∀ i, specialCell hm hnm i a ≠ some x := by
  simp only [freeColors, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
    Finset.mem_singleton, true_and, not_or] at hx
  exact ⟨hx.2.1, fun i hi => by
    rcases special_cases hm hnm hi with ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩
    · exact hx.1 he
    · exact hx.2.2.2 he
    · exact hx.2.2.1 he⟩

include hm hnm hn in
theorem small_locating (cycle : Bool) :
    ∃ c : Fin m × Fin n → Fin (m + 1), IsLocating (Grid m (chain cycle n)) c := by
  obtain ⟨f, hf, hspec⟩ := complete_columns (nextCol n) (shortLabel hnm) (specialCell hm hnm)
    (special_proper hm hnm hn)
    (fun a => (adjacent_offset_ne hn a).1)
    (freeRows hm hnm) (freeColors hnm)
    (fun a => by rw [freeRows_card hm hnm hn, freeColors_card hnm hn])
    (fun a => by rw [freeColors_card hnm hn]; omega)
    (freeRows_iff hm hnm) (freeColors_avoid hm hnm)
  let c (v : Fin m × Fin n) := f v.1 v.2
  have hH := chain_preconnected cycle n
  have hG := preconnected_top.boxProd (G := (⊤ : SimpleGraph (Fin m))) hH
  have hle : chain cycle n ≤ cycleGraph n := by cases cycle; exact pathGraph_le_cycleGraph; exact le_rfl
  have hp : Proper (Grid m (chain cycle n)) c := by
    rintro ⟨i, a⟩ ⟨r, b⟩ h he
    rcases boxProd_adj.mp h with ⟨hir, hab⟩ | ⟨hab, hir⟩
    · change a = b at hab
      subst b
      exact hir (hf.column _ _ _ _ rfl (congrArg some he.symm))
    · change i = r at hir
      subst r
      rcases (cycle_adj_iff_next (by omega) a b).mp (hle hab) with e | e
      · subst b
        exact hf.edge _ _ _ rfl (congrArg some he.symm)
      · subst a
        exact hf.edge _ _ _ rfl (congrArg some he)
  have hmiss (a : Fin n) : ¬Present c (shortLabel hnm a) a := by
    rintro ⟨i, hi⟩
    exact hf.excludes i a (congrArg some hi)
  have hs : Function.Surjective c := by
    intro x
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    by_cases h : x = shortLabel hnm a
    · have he : x ≠ shortLabel hnm b := by
        intro he
        have hEq : a = b := shortLabel_injective hnm (h.symm.trans he)
        have hv := congrArg (fun j : Fin n => j.val) hEq
        contradiction
      obtain ⟨i, hi⟩ := present_of_ne_missing hp (hmiss b) he
      exact ⟨(i, b), hi⟩
    · obtain ⟨i, hi⟩ := present_of_ne_missing hp (hmiss a) h
      exact ⟨(i, a), hi⟩
  have hrow {i : Fin m} {a : Fin n}
      (h : colorDist (Grid m (chain cycle n)) c (i, a) (shortLabel hnm a) = 1) :
      i = specialRow hm hnm a := by
    have hne : c (i, a) ≠ shortLabel hnm a := fun e => hmiss a ⟨i, e⟩
    obtain ⟨⟨r, b⟩, hb, had⟩ := (colorDist_eq_one_iff hG hs hne).mp h
    rcases boxProd_adj.mp had with ⟨_, hab⟩ | ⟨hab, hr⟩
    · change a = b at hab
      subst b
      exact (hmiss a ⟨r, hb⟩).elim
    · change i = r at hr
      subst r
      rcases (cycle_adj_iff_next (by omega) a b).mp (hle hab) with h₀ | h₁
      · subst b
        rw [nextCol_apply] at hb
        have hspec' := (special_mates hm hnm hn (a + 1)).1
        rw [add_sub_cancel_right] at hspec'
        exact column_injective hp (a + 1) (hb.trans (hspec _ _ _ hspec').symm)
      · have ha : a = b + 1 := h₁
        subst a
        exact column_injective hp b (hb.trans (hspec _ _ _ (special_mates hm hnm hn b).2.2).symm)
  refine ⟨c, hp, hs, ?_⟩
  rintro ⟨i, a⟩ ⟨r, b⟩ h
  have he : c (i, a) = c (r, b) :=
    ((colorDist_eq_zero_iff hG hs).1 ((congrFun h (c (i, a))).symm.trans colorDist_own)).symm
  by_cases hab : a = b
  · subst b
    exact Prod.ext (column_injective hp a he) rfl
  · have near (i r : Fin m) (a b : Fin n) (hab : a ≠ b)
        (h : (fun x => colorDist (Grid m (chain cycle n)) c (i, a) x) =
          (fun x => colorDist (Grid m (chain cycle n)) c (r, b) x)) :
        i = specialRow hm hnm a := by
      have hlabel : shortLabel hnm a ≠ shortLabel hnm b := fun e => hab (shortLabel_injective hnm e)
      have hp' := present_of_ne_missing hp (hmiss b) hlabel
      have hx : c (r, b) ≠ shortLabel hnm a := fun e =>
        hmiss a ⟨i, ((colorDist_eq_zero_iff hG hs).mp
          ((congrFun h (shortLabel hnm a)).trans ((colorDist_eq_zero_iff hG hs).mpr e)))⟩
      apply hrow
      have hdist := congrFun h (shortLabel hnm a)
      change colorDist (Grid m (chain cycle n)) c (i, a) (shortLabel hnm a) = _ at hdist
      rw [hdist, column_dist hH hs hp']
      simp [hx]
    have hi := near i r a b hab h
    have hr := near r i b a (Ne.symm hab) h.symm
    subst i
    subst r
    have ha := hspec _ _ _ (special_mates hm hnm hn a).2.1
    have hb := hspec _ _ _ (special_mates hm hnm hn b).2.1
    have hh : a + 2 = b + 2 := shortLabel_injective hnm (ha.symm.trans (he.trans hb))
    exact (hab (add_right_cancel hh)).elim

#print axioms small_locating

end Locating321730
```

### `LocatingSingleton.lean`

```lean
import LocatingRuns

open SimpleGraph

namespace Locating321730

variable {m n : ℕ}

def rowA (hm : 7 ≤ m) : Fin m := ⟨2, by omega⟩
def rowB (hm : 7 ≤ m) : Fin m := ⟨0, by omega⟩
def colA (hn : 4 ≤ n) : Fin n := ⟨0, by omega⟩
def nextToA (hn : 4 ≤ n) : Fin n := ⟨1, by omega⟩

def rowIncrement (r i : Fin m) : ℕ := if i = r then 0 else 1

theorem rowIncrement_le (r i : Fin m) : rowIncrement r i ≤ 1 := by
  unfold rowIncrement
  split <;> omega

theorem rowIncrement_zero {r i : Fin m} : rowIncrement r i = 0 ↔ i = r := by
  by_cases h : i = r <;> simp [rowIncrement, h]

theorem rowIncrement_sum_pos (hm : 7 ≤ m) (i : Fin m) :
    1 ≤ rowIncrement (rowA hm) i + rowIncrement (rowB hm) i := by
  have hne : rowA hm ≠ rowB hm := by
    intro h
    have he := congrArg Fin.val h
    contradiction
  unfold rowIncrement
  split <;> split <;> omega

def regular (hm : 7 ≤ m) (s : ℕ) (i : Fin m) : Fin m :=
  ⟨(i.val + s) % m, Nat.mod_lt _ (by omega)⟩

theorem regular_val (hm : 7 ≤ m) {s : ℕ} (hs : s < m) (i : Fin m) :
    (regular hm s i).val = if i.val + s < m then i.val + s else i.val + s - m := by
  change (i.val + s) % m = _
  rw [Nat.add_mod_eq_ite, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt hs]
  split <;> split <;> omega

theorem regular_injective (hm : 7 ≤ m) {s : ℕ} (hs : s < m) :
    Function.Injective (regular hm s) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  rw [regular_val hm hs, regular_val hm hs] at hv
  have hi := i.isLt
  have hj := j.isLt
  split at hv <;> split at hv <;> omega

theorem regular_shift_injective (hm : 7 ≤ m) {s t : ℕ} (hs : s < m) (ht : t < m)
    {i : Fin m} (h : regular hm s i = regular hm t i) : s = t := by
  have hv := congrArg Fin.val h
  rw [regular_val hm hs, regular_val hm ht] at hv
  split at hv <;> split at hv <;> omega

theorem pair_separates_path (hm : 7 ≤ m) (hn : 4 ≤ n)
    (i r : Fin m) (a b : Fin n)
    (hA : (KP m n).dist (i, a) (rowA hm, colA hn) = (KP m n).dist (r, b) (rowA hm, colA hn))
    (hB : (KP m n).dist (i, a) (rowB hm, colA hn) = (KP m n).dist (r, b) (rowB hm, colA hn)) :
    a = b := by
  have hH := pathGraph_preconnected n
  simp only [KP, product_dist hH, path_dist, gap] at hA hB
  change rowIncrement (rowA hm) i + (a.val - 0 + (0 - a.val)) =
    rowIncrement (rowA hm) r + (b.val - 0 + (0 - b.val)) at hA
  change rowIncrement (rowB hm) i + (a.val - 0 + (0 - a.val)) =
    rowIncrement (rowB hm) r + (b.val - 0 + (0 - b.val)) at hB
  have hi := rowIncrement_sum_pos hm i
  have hr := rowIncrement_sum_pos hm r
  have hAi := rowIncrement_le (rowA hm) i
  have hAr := rowIncrement_le (rowA hm) r
  have hBi := rowIncrement_le (rowB hm) i
  have hBr := rowIncrement_le (rowB hm) r
  exact Fin.ext (by omega)

def singletonColor (hm : 7 ≤ m) (hn : 4 ≤ n)
    (b : Fin n) (σ : Fin n → ℕ) (v : Fin m × Fin n) : Fin (m + 2) :=
  if v = (rowA hm, colA hn) then ⟨m, by omega⟩
  else if v = (rowB hm, b) then ⟨m + 1, by omega⟩
  else ⟨(regular hm (σ v.2) v.1).val, by have := (regular hm (σ v.2) v.1).isLt; omega⟩

theorem singleton_locating (hm : 7 ≤ m) (hn : 4 ≤ n) {H : SimpleGraph (Fin n)}
    (hH : H.Preconnected) (b : Fin n) (σ : Fin n → ℕ) (hσ : ∀ j, σ j < m)
    (hshift : ∀ a d, H.Adj a d → σ a ≠ σ d)
    (hfree : ∃ j, j ≠ colA hn ∧ j ≠ b)
    (sep : ∀ (i r : Fin m) (j k : Fin n),
      (i, j) ≠ (rowA hm, colA hn) → (i, j) ≠ (rowB hm, b) →
      (r, k) ≠ (rowA hm, colA hn) → (r, k) ≠ (rowB hm, b) →
      regular hm (σ j) i = regular hm (σ k) r →
      (Grid m H).dist (i, j) (rowA hm, colA hn) = (Grid m H).dist (r, k) (rowA hm, colA hn) →
      (Grid m H).dist (i, j) (rowB hm, b) = (Grid m H).dist (r, k) (rowB hm, b) → j = k) :
    IsLocating (Grid m H) (singletonColor hm hn b σ) := by
  let A : Fin m × Fin n := (rowA hm, colA hn)
  let B : Fin m × Fin n := (rowB hm, b)
  let aMark : Fin (m + 2) := ⟨m, by omega⟩
  let bMark : Fin (m + 2) := ⟨m + 1, by omega⟩
  let c := singletonColor hm hn b σ
  have hAB : A ≠ B := by
    intro e
    have h := congrArg (fun v : Fin m × Fin n => v.1.val) e
    contradiction
  have hcA (v : Fin m × Fin n) : c v = aMark ↔ v = A := by
    unfold c singletonColor
    change (if v = A then aMark else if v = B then bMark else _) = aMark ↔ _
    split
    · simp_all
    · split
      · simp_all [aMark, bMark, Fin.ext_iff]
      · rename_i hv _
        have hlt := (regular hm (σ v.2) v.1).isLt
        rw [Fin.ext_iff]
        change ((regular hm (σ v.2) v.1).val = m) ↔ v = A
        simp [ne_of_lt hlt, hv]
  have hcB (v : Fin m × Fin n) : c v = bMark ↔ v = B := by
    unfold c singletonColor
    change (if v = A then aMark else if v = B then bMark else _) = bMark ↔ _
    split
    · rename_i h
      simp [h, hAB, aMark, bMark, Fin.ext_iff]
    · split
      · simp_all
      · rename_i _ hv
        have hlt := (regular hm (σ v.2) v.1).isLt
        rw [Fin.ext_iff]
        change ((regular hm (σ v.2) v.1).val = m + 1) ↔ v = B
        simp [ne_of_lt (hlt.trans (Nat.lt_succ_self _)), hv]
  have hcR {v : Fin m × Fin n} (ha : v ≠ A) (hb : v ≠ B) :
      (c v).val = (regular hm (σ v.2) v.1).val := by
    change (singletonColor hm hn b σ v).val = _
    unfold singletonColor
    change (if v = A then aMark else if v = B then bMark else _).val = _
    simp [ha, hb]
  have hregular {u v : Fin m × Fin n} (huA : u ≠ A) (huB : u ≠ B)
      (he : c u = c v) :
      v ≠ A ∧ v ≠ B ∧ regular hm (σ u.2) u.1 = regular hm (σ v.2) v.1 := by
    have hvA : v ≠ A := fun h => huA ((hcA u).mp (he.trans ((hcA v).mpr h)))
    have hvB : v ≠ B := fun h => huB ((hcB u).mp (he.trans ((hcB v).mpr h)))
    exact ⟨hvA, hvB, Fin.ext ((hcR huA huB).symm.trans ((congrArg Fin.val he).trans (hcR hvA hvB)))⟩
  have hs : Function.Surjective c := by
    intro x
    by_cases hx : x.val < m
    · obtain ⟨j, hjA, hjB⟩ := hfree
      have hsurj : Function.Surjective (regular hm (σ j)) :=
        Finite.surjective_of_injective (regular_injective hm (hσ j))
      obtain ⟨i, hi⟩ := hsurj ⟨x.val, hx⟩
      have hvA : (i, j) ≠ A := fun e => hjA (congrArg Prod.snd e)
      have hvB : (i, j) ≠ B := fun e => hjB (congrArg Prod.snd e)
      exact ⟨(i, j), Fin.ext ((hcR hvA hvB).trans (congrArg Fin.val hi))⟩
    · have hcases : x = aMark ∨ x = bMark := by
        have := x.isLt
        rw [Fin.ext_iff, Fin.ext_iff]
        change x.val = m ∨ x.val = m + 1
        omega
      rcases hcases with rfl | rfl
      · exact ⟨A, (hcA A).mpr rfl⟩
      · exact ⟨B, (hcB B).mpr rfl⟩
  have hG := preconnected_top.boxProd (G := (⊤ : SimpleGraph (Fin m))) hH
  refine ⟨?_, hs, ?_⟩
  · rintro ⟨i, j⟩ ⟨r, k⟩ had he
    by_cases hA : (i, j) = A
    · exact (Grid m H).ne_of_adj had (hA.trans ((hcA _).mp (he.symm.trans ((hcA _).mpr hA))).symm)
    by_cases hB : (i, j) = B
    · exact (Grid m H).ne_of_adj had (hB.trans ((hcB _).mp (he.symm.trans ((hcB _).mpr hB))).symm)
    obtain ⟨_, _, hR⟩ := hregular hA hB he
    dsimp only [Prod.fst, Prod.snd] at hR
    rcases boxProd_adj.mp had with ⟨hne, hcol⟩ | ⟨hcol, hrow⟩
    · change j = k at hcol
      subst k
      exact hne (regular_injective hm (hσ j) hR)
    · change i = r at hrow
      subst r
      exact hshift j k hcol (regular_shift_injective hm (hσ j) (hσ k) hR)
  · rintro ⟨i, j⟩ ⟨r, k⟩ he
    have hcEq : c (i, j) = c (r, k) :=
      ((colorDist_eq_zero_iff hG hs).mp ((congrFun he (c (i, j))).symm.trans colorDist_own)).symm
    by_cases hA : (i, j) = A
    · exact hA.trans ((hcA _).mp (hcEq.symm.trans ((hcA _).mpr hA))).symm
    by_cases hB : (i, j) = B
    · exact hB.trans ((hcB _).mp (hcEq.symm.trans ((hcB _).mpr hB))).symm
    obtain ⟨hrA, hrB, hR⟩ := hregular hA hB hcEq
    have hdistA := congrFun he aMark
    have hdistB := congrFun he bMark
    change colorDist (Grid m H) c (i, j) aMark = colorDist (Grid m H) c (r, k) aMark at hdistA
    change colorDist (Grid m H) c (i, j) bMark = colorDist (Grid m H) c (r, k) bMark at hdistB
    rw [colorDist_singleton hcA, colorDist_singleton hcA] at hdistA
    rw [colorDist_singleton hcB, colorDist_singleton hcB] at hdistB
    have hcol := sep i r j k hA hB hrA hrB hR hdistA hdistB
    subst k
    exact Prod.ext (regular_injective hm (hσ j) hR) rfl

theorem path_large_locating (hm : 7 ≤ m) (hn : 4 ≤ n) :
    ∃ c : Fin m × Fin n → Fin (m + 2), IsLocating (KP m n) c := by
  let σ (j : Fin n) := j.val % 2
  refine ⟨singletonColor hm hn (colA hn) σ,
    singleton_locating hm hn (pathGraph_preconnected n) (colA hn) σ
      (fun j => by dsimp [σ]; omega) ?_ ?_ ?_⟩
  · intro a b hab
    rw [pathGraph_adj] at hab
    dsimp [σ]
    omega
  · have hne : nextToA hn ≠ colA hn := by
      intro h
      have he := congrArg Fin.val h
      contradiction
    exact ⟨nextToA hn, hne, hne⟩
  · intro i r j k _ _ _ _ _ hA hB
    exact pair_separates_path hm hn i r j k hA hB

#print axioms path_large_locating

end Locating321730
```

### `LocatingCycleShifts.lean`

```lean
import LocatingSingleton

open SimpleGraph

namespace Locating321730

variable {m n : ℕ}

/-- The odd-cycle shifts are increased by two so that all of them are natural numbers. -/
def cycleShift (n j : ℕ) : ℕ :=
  if n % 2 = 0 then j % 2
  else if j = 0 then 6
  else if j = 1 then 5
  else if j = n / 2 then 0
  else if j = n / 2 + 1 then 2
  else if j = n / 2 + 2 then 4
  else if j < n / 2 + 1 then 2 + (n / 2 + 2 - j) % 2
  else 2 + (j - n / 2) % 2

theorem cycleShift_le (n j : ℕ) : cycleShift n j ≤ 6 := by
  unfold cycleShift
  split_ifs <;> omega

theorem cycleShift_edge (hn : 9 ≤ n) {a b : Fin n} (h : (cycleGraph n).Adj a b) :
    cycleShift n a.val ≠ cycleShift n b.val := by
  rw [cycle_adj_iff_gap (by omega)] at h
  have ha := a.isLt
  have hb := b.isLt
  have ordered (j k : ℕ) (hjk : j < k) (hk : k < n) (h : k = j + 1 ∨ k + 1 = n ∧ j = 0) :
      cycleShift n j ≠ cycleShift n k := by
    unfold cycleShift
    split
    · omega
    · split_ifs <;> omega
  unfold gap at h
  by_cases hab : a.val < b.val
  · exact ordered a.val b.val hab hb (by omega)
  · exact Ne.symm (ordered b.val a.val (by omega) ha (by omega))

theorem cycleShift_marked (hm : 7 ≤ m) (n : ℕ) :
    regular hm (cycleShift n 0) (rowB hm) ≠ regular hm (cycleShift n 1) (rowA hm) := by
  intro he
  have h := congrArg Fin.val he
  by_cases hn' : n % 2 = 0
  · simp [cycleShift, hn'] at h
    rw [regular_val hm (show 0 < m by omega), regular_val hm (show 1 < m by omega)] at h
    change (if 0 + 0 < m then 0 + 0 else 0 + 0 - m) =
      (if 2 + 1 < m then 2 + 1 else 2 + 1 - m) at h
    split at h <;> split at h <;> omega
  · have h0 : cycleShift n 0 = 6 := by simp [cycleShift, hn']
    have h1 : cycleShift n 1 = 5 := by simp [cycleShift, hn']
    rw [h0, h1, regular_val hm (show 6 < m by omega), regular_val hm (show 5 < m by omega)] at h
    change (if 0 + 6 < m then 0 + 6 else 0 + 6 - m) =
      (if 2 + 5 < m then 2 + 5 else 2 + 5 - m) at h
    split at h <;> split at h <;> omega

theorem cycleShift_reflected (hm : 7 ≤ m) (hn : 9 ≤ n)
    {j k : ℕ} (hj : 2 ≤ j) (hmid : j ≤ n / 2) (_hk : k < n) (hs : j + k = n + 1) :
    regular hm (cycleShift n j) (rowA hm) ≠ regular hm (cycleShift n k) (rowB hm) := by
  intro he
  have h := congrArg Fin.val he
  rw [regular_val hm ((cycleShift_le _ _).trans_lt (by omega)),
    regular_val hm ((cycleShift_le _ _).trans_lt (by omega))] at h
  change (if 2 + cycleShift n j < m then 2 + cycleShift n j else 2 + cycleShift n j - m) =
    (if 0 + cycleShift n k < m then 0 + cycleShift n k else 0 + cycleShift n k - m) at h
  by_cases heven : n % 2 = 0
  · simp only [cycleShift, heven, ite_true] at h
    split at h <;> split at h <;> omega
  · have hj₁ : j ≠ 0 := by omega
    have hj₂ : j ≠ 1 := by omega
    have hj₃ : j ≠ n / 2 + 1 := by omega
    have hj₄ : j ≠ n / 2 + 2 := by omega
    have hj₅ : j < n / 2 + 1 := by omega
    have hk₁ : k ≠ 0 := by omega
    have hk₂ : k ≠ 1 := by omega
    have hk₃ : k ≠ n / 2 := by omega
    have hk₄ : k ≠ n / 2 + 1 := by omega
    have hk₅ : ¬ k < n / 2 + 1 := by omega
    have hjs : cycleShift n j = if j = n / 2 then 0 else 2 + (n / 2 + 2 - j) % 2 := by
      simp [cycleShift, heven, hj₁, hj₂, hj₃, hj₄, hj₅]
    have hks : cycleShift n k = if k = n / 2 + 2 then 4 else 2 + (k - n / 2) % 2 := by
      simp [cycleShift, heven, hk₁, hk₂, hk₃, hk₄, hk₅]
    rw [hjs, hks] at h
    split_ifs at h <;> omega

theorem cycleShift_mid (hn : 9 ≤ n) (hodd : n % 2 = 1) :
    cycleShift n (n / 2) = 0 ∧ cycleShift n (n / 2 + 1) = 2 ∧
      cycleShift n (n / 2 + 2) = 4 := by
  have h₀ : n / 2 ≠ 0 := by omega
  have h₁ : n / 2 ≠ 1 := by omega
  simp [cycleShift, hodd, h₀, h₁]

end Locating321730
```

### `LocatingCycleUpper.lean`

```lean
import LocatingCycleShifts

open SimpleGraph

namespace Locating321730

variable {m n : ℕ}

/-- The two marked columns, the two arcs, and the odd antipode. -/
private def Profile (n j a b : ℕ) : Prop :=
  (j = 0 ∧ a = 0 ∧ b = 1) ∨
  (j = 1 ∧ a = 1 ∧ b = 0) ∨
  (2 ≤ j ∧ j ≤ n / 2 ∧ a = j ∧ b = j - 1) ∨
  (n % 2 = 1 ∧ j = n / 2 + 1 ∧ a = n / 2 ∧ b = n / 2) ∨
  (n / 2 < j ∧ a = n - j ∧ b = n + 1 - j)

private theorem column_profiles (hn : 4 ≤ n) (j : Fin n) :
    Profile n j.val (cycleGap j (colA hn)) (cycleGap j (nextToA hn)) := by
  unfold Profile
  have hj := j.isLt
  have ha : cycleGap j (colA hn) = min j.val (n - j.val) := by
    unfold cycleGap gap
    change min (j.val - 0 + (0 - j.val)) (n - (j.val - 0 + (0 - j.val))) = _
    simp
  have hb : cycleGap j (nextToA hn) =
      min (j.val - 1 + (1 - j.val)) (n - (j.val - 1 + (1 - j.val))) := rfl
  rw [ha, hb]
  by_cases h₀ : j.val = 0
  · exact .inl ⟨h₀, by simp [h₀], by simp [h₀]; omega⟩
  by_cases h₁ : j.val = 1
  · exact .inr (.inl ⟨h₁, by simp [h₁]; omega, by simp [h₁]⟩)
  have h2 : 2 ≤ j.val := by omega
  have hsub : 1 - j.val = 0 := by omega
  rw [hsub, Nat.add_zero]
  by_cases ht : j.val ≤ n / 2
  · have ha' : j.val ≤ n - j.val := by omega
    have hb' : j.val - 1 ≤ n - (j.val - 1) := by omega
    exact .inr (.inr (.inl ⟨h2, ht, min_eq_left ha', min_eq_left hb'⟩))
  by_cases hmid : n % 2 = 1 ∧ j.val = n / 2 + 1
  · have ha' : n - j.val ≤ j.val := by omega
    have hb' : j.val - 1 ≤ n - (j.val - 1) := by omega
    exact .inr (.inr (.inr (.inl ⟨hmid.1, hmid.2, by rw [min_eq_right ha']; omega,
      by rw [min_eq_left hb']; omega⟩)))
  · have ha' : n - j.val ≤ j.val := by omega
    have hb' : n - (j.val - 1) ≤ j.val - 1 := by omega
    exact .inr (.inr (.inr (.inr ⟨by omega, min_eq_right ha', by rw [min_eq_right hb']; omega⟩)))

private theorem collision_profiles (hn : 4 ≤ n) {j k A B A' B' : ℕ}
    (hjk : j < k) (hk : k < n)
    (jp : Profile n j A B) (kp : Profile n k A' B')
    {a₀ b₀ a₁ b₁ : ℕ}
    (ha₀ : a₀ ≤ 1) (hb₀ : b₀ ≤ 1) (ha₁ : a₁ ≤ 1) (hb₁ : b₁ ≤ 1)
    (hs₀ : 1 ≤ a₀ + b₀) (hs₁ : 1 ≤ a₁ + b₁)
    (hmark₀ : j = 0 → a₀ = 1) (hmark₁ : k = 1 → b₁ = 1)
    (hA : a₀ + A = a₁ + A') (hB : b₀ + B = b₁ + B') :
    (j = 0 ∧ k = 1 ∧ b₀ = 0 ∧ a₁ = 0) ∨
    (2 ≤ j ∧ j ≤ n / 2 ∧ j + k = n + 1 ∧ a₀ = 0 ∧ b₁ = 0) ∨
    (n % 2 = 1 ∧ j = n / 2 ∧ k = n / 2 + 1 ∧ a₀ = 1 ∧ b₁ = 0) ∨
    (n % 2 = 1 ∧ j = n / 2 + 1 ∧ k = n / 2 + 2 ∧ a₀ = 0 ∧ b₁ = 1) := by
  unfold Profile at jp kp
  rcases jp with ⟨jh, ja, jb⟩ | ⟨jh, ja, jb⟩ | ⟨jh, ji, ja, jb⟩ |
    ⟨jh, ji, ja, jb⟩ | ⟨jh, ja, jb⟩
  · have ham := hmark₀ jh
    rcases kp with ⟨kh, ka, kb⟩ | ⟨kh, ka, kb⟩ | ⟨kh, ki, ka, kb⟩ |
      ⟨kh, ki, ka, kb⟩ | ⟨kh, ka, kb⟩
    · exfalso; omega
    · have hbm := hmark₁ kh
      exact .inl ⟨jh, kh, by omega, by omega⟩
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
  · rcases kp with ⟨kh, ka, kb⟩ | ⟨kh, ka, kb⟩ | ⟨kh, ki, ka, kb⟩ |
      ⟨kh, ki, ka, kb⟩ | ⟨kh, ka, kb⟩ <;>
      exfalso <;> omega
  · rcases kp with ⟨kh, ka, kb⟩ | ⟨kh, ka, kb⟩ | ⟨kh, ki, ka, kb⟩ |
      ⟨kh, ki, ka, kb⟩ | ⟨kh, ka, kb⟩
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact .inr (.inr (.inl ⟨kh, by omega, ki, by omega, by omega⟩))
    · exact .inr (.inl ⟨jh, ji, by omega, by omega, by omega⟩)
  · rcases kp with ⟨kh, ka, kb⟩ | ⟨kh, ka, kb⟩ | ⟨kh, ki, ka, kb⟩ |
      ⟨kh, ki, ka, kb⟩ | ⟨kh, ka, kb⟩
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact .inr (.inr (.inr ⟨jh, ji, by omega, by omega, by omega⟩))
  · rcases kp with ⟨kh, ka, kb⟩ | ⟨kh, ka, kb⟩ | ⟨kh, ki, ka, kb⟩ |
      ⟨kh, ki, ka, kb⟩ | ⟨kh, ka, kb⟩ <;>
      exfalso <;> omega

private theorem cycle_no_collision_ordered (hm : 7 ≤ m) (hn : 9 ≤ n)
    (h4 : 4 ≤ n) (i r : Fin m) (j k : Fin n) (hjk : j.val < k.val)
    (h₀ : (i, j) ≠ (rowA hm, colA h4))
    (h₁ : (r, k) ≠ (rowB hm, nextToA h4))
    (he : regular hm (cycleShift n j.val) i = regular hm (cycleShift n k.val) r)
    (hA : (KC m n).dist (i, j) (rowA hm, colA h4) = (KC m n).dist (r, k) (rowA hm, colA h4))
    (hB : (KC m n).dist (i, j) (rowB hm, nextToA h4) = (KC m n).dist (r, k) (rowB hm, nextToA h4)) :
    False := by
  have hcc := cycleGraph_preconnected (n := n)
  simp only [KC, product_dist hcc, cycle_dist (show 2 ≤ n by omega)] at hA hB
  change rowIncrement (rowA hm) i + cycleGap j (colA h4) =
    rowIncrement (rowA hm) r + cycleGap k (colA h4) at hA
  change rowIncrement (rowB hm) i + cycleGap j (nextToA h4) =
    rowIncrement (rowB hm) r + cycleGap k (nextToA h4) at hB
  have hmark₀ (h : j.val = 0) : rowIncrement (rowA hm) i = 1 := by
    have hne : i ≠ rowA hm := fun e => h₀ (Prod.ext e (Fin.ext h))
    simp [rowIncrement, hne]
  have hmark₁ (h : k.val = 1) : rowIncrement (rowB hm) r = 1 := by
    have hne : r ≠ rowB hm := fun e => h₁ (Prod.ext e (Fin.ext h))
    simp [rowIncrement, hne]
  have hc := collision_profiles h4 hjk k.isLt (column_profiles h4 j) (column_profiles h4 k)
    (rowIncrement_le _ _) (rowIncrement_le _ _)
    (rowIncrement_le _ _) (rowIncrement_le _ _) (rowIncrement_sum_pos hm i)
    (rowIncrement_sum_pos hm r) hmark₀ hmark₁ hA hB
  rcases hc with ⟨hj, hk, hi, hr⟩ | ⟨hj, hj', hk, hi, hr⟩ |
    ⟨hodd, hj, hk, hi, hr⟩ | ⟨hodd, hj, hk, hi, hr⟩
  · rw [hj, hk, rowIncrement_zero.mp hi, rowIncrement_zero.mp hr] at he
    exact cycleShift_marked hm n he
  · rw [rowIncrement_zero.mp hi, rowIncrement_zero.mp hr] at he
    exact cycleShift_reflected hm hn hj hj' k.isLt hk he
  · obtain ⟨hmid₀, hmid, _⟩ := cycleShift_mid hn hodd
    rw [hj, hk, hmid₀, hmid, rowIncrement_zero.mp hr] at he
    have hval : regular hm 2 (rowB hm) = regular hm 0 (rowA hm) := by
      apply Fin.ext
      rfl
    have hr : i = rowA hm := regular_injective hm (show 0 < m by omega) (he.trans hval)
    have hzero := rowIncrement_zero.mpr hr
    omega
  · obtain ⟨_, hmid, hmid₁⟩ := cycleShift_mid hn hodd
    rw [hj, hk, hmid, hmid₁, rowIncrement_zero.mp hi] at he
    have hval : regular hm 2 (rowA hm) = regular hm 4 (rowB hm) := by
      apply Fin.ext
      rfl
    have hr' : r = rowB hm := regular_injective hm (show 4 < m by omega) (he.symm.trans hval)
    have hzero := rowIncrement_zero.mpr hr'
    omega

theorem cycle_large_locating (hm : 7 ≤ m) (hn : 9 ≤ n) :
    ∃ c : Fin m × Fin n → Fin (m + 2), IsLocating (KC m n) c := by
  have h4 : 4 ≤ n := by omega
  let σ (j : Fin n) := cycleShift n j.val
  refine ⟨singletonColor hm h4 (nextToA h4) σ,
    singleton_locating hm h4 cycleGraph_preconnected (nextToA h4) σ
      (fun j => (cycleShift_le _ _).trans_lt (by omega)) (fun _ _ => cycleShift_edge hn) ?_ ?_⟩
  · refine ⟨⟨2, by omega⟩, ?_, ?_⟩ <;>
      intro e <;> have he := congrArg Fin.val e
    · change (2 : ℕ) = 0 at he
      omega
    · change (2 : ℕ) = 1 at he
      omega
  · intro i r j k h₀ h₁ h₂ h₃ he hA hB
    apply Fin.ext
    rcases lt_trichotomy j.val k.val with h | h | h
    · exact (cycle_no_collision_ordered hm hn h4 i r j k h h₀ h₃ he hA hB).elim
    · exact h
    · exact (cycle_no_collision_ordered hm hn h4 r i k j h h₂ h₁ he.symm hA.symm hB.symm).elim

#print axioms cycle_large_locating

end Locating321730
```

### `LocatingConjecture.lean`

```lean
import LocatingSmall
import LocatingCycleUpper

open SimpleGraph

namespace Locating321730

private theorem locChrom_chain {m n : ℕ} (cycle : Bool) (hm : 7 ≤ m) (hn : 4 ≤ n) :
    locChrom (Grid m (chain cycle n)) = if n ≤ m + 1 then m + 1 else m + 2 := by
  have hH := chain_preconnected cycle n
  obtain ⟨c, hc⟩ := locChrom_attained (preconnected_top.boxProd hH :
    (Grid m (chain cycle n)).Preconnected)
  by_cases hsmall : n ≤ m + 1
  · simp only [hsmall, ite_true]
    let : NeZero n := ⟨by omega⟩
    obtain ⟨f, hf⟩ := small_locating hm hsmall hn cycle
    exact le_antisymm (locChrom_le hf) (clique_lower hH (by omega) (by omega) hc)
  · simp only [hsmall, ite_false]
    have hlarge : m + 2 ≤ n := by omega
    have hcol : ∃ f : Fin m × Fin n → Fin (m + 2), IsLocating (Grid m (chain cycle n)) f := by
      cases cycle
      · exact path_large_locating hm hn
      · exact cycle_large_locating hm (by omega)
    obtain ⟨f, hf⟩ := hcol
    exact le_antisymm (locChrom_le hf) (many_columns_lower cycle (by omega) (by omega) hlarge hc)

theorem locChrom_KC (m n : ℕ) (hm : 7 ≤ m) (hn : 4 ≤ n) :
    locChrom (KC m n) = if n ≤ m + 1 then m + 1 else m + 2 :=
  locChrom_chain true hm hn

theorem locChrom_KP (m n : ℕ) (hm : 7 ≤ m) (hn : 4 ≤ n) :
    locChrom (KP m n) = if n ≤ m + 1 then m + 1 else m + 2 :=
  locChrom_chain false hm hn

theorem mathdb_321730 :
    ∃ M N : ℕ, ∀ m n : ℕ, M ≤ m → N ≤ n →
      locChrom (KC m n) = locChrom (KP m n) := by
  refine ⟨7, 4, ?_⟩
  intro m n hm hn
  rw [locChrom_KC m n hm hn, locChrom_KP m n hm hn]

#check mathdb_321730
#check locChrom_KC
#check locChrom_KP
#print axioms mathdb_321730
#print axioms locChrom_KC
#print axioms locChrom_KP

end Locating321730
```
