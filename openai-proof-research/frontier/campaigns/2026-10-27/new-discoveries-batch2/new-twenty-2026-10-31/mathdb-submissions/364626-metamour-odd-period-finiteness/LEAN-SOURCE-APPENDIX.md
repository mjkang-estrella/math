# Exact Lean appendix for MathDB 364626

Eight canonical author modules.

## MetaBase.lean

```lean
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Ring.Parity

#eval Lean.versionString

namespace Metamour

variable {V : Type*}

def metamour (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ¬ G.Adj u v ∧ ∃ w, G.Adj u w ∧ G.Adj v w
  symm := ⟨by
    intro u v h
    obtain ⟨hne, hna, w, hu, hv⟩ := h
    exact ⟨hne.symm, fun h => hna h.symm, w, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem meta_adj_iff_edist (G : SimpleGraph V) (u v : V) :
    (metamour G).Adj u v ↔ G.edist u v = 2 :=
  G.edist_eq_two_iff.symm

def phase (G : SimpleGraph V) : ℕ → SimpleGraph V
  | 0 => G
  | t + 1 => metamour (phase G t)

@[simp] theorem phase_zero (G : SimpleGraph V) : phase G 0 = G := rfl

@[simp] theorem phase_succ (G : SimpleGraph V) (t : ℕ) :
    phase G (t + 1) = metamour (phase G t) := rfl

theorem phase_add (G : SimpleGraph V) (a b : ℕ) :
    phase G (a + b) = phase (phase G a) b := by
  induction b with
  | zero => simp
  | succ b ih => simp only [Nat.add_succ, phase_succ, ih]

def ExactPeriod (G : SimpleGraph V) (k : ℕ) : Prop :=
  0 < k ∧ phase G k = G ∧ ∀ j, 0 < j → j < k → phase G j ≠ G

theorem phase_shift {G : SimpleGraph V} {k : ℕ} (hr : phase G k = G) (t : ℕ) :
    phase G (t + k) = phase G t := by
  rw [Nat.add_comm, phase_add, hr]

theorem phase_return {G : SimpleGraph V} {k : ℕ} (hr : phase G k = G) (t : ℕ) :
    phase (phase G t) k = phase G t := by
  rw [← phase_add, phase_shift hr]

theorem meta_reachable {G : SimpleGraph V} {u v : V} (h : (metamour G).Reachable u v) :
    G.Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | cons hadj _ ih =>
    obtain ⟨_, _, w, hu, hv⟩ := hadj
    exact hu.reachable.trans (hv.symm.reachable.trans ih)

theorem phase_reachable {G : SimpleGraph V} {u v : V} {t : ℕ}
    (h : (phase G t).Reachable u v) : G.Reachable u v := by
  induction t with
  | zero => exact h
  | succ t ih => exact ih (meta_reachable h)

theorem phase_preconnected {G : SimpleGraph V} {k : ℕ} (hc : G.Preconnected) (hk : 0 < k)
    (hr : phase G k = G) (t : ℕ) : (phase G t).Preconnected := by
  intro u v
  have hz : (phase G (k * t)).Reachable u v := by
    induction t with
    | zero => exact hc u v
    | succ t ih => simpa only [Nat.mul_succ, phase_shift hr] using ih
  have ht : t ≤ k * t := by
    simpa using Nat.mul_le_mul_right t (show 1 ≤ k by omega)
  have he : (phase (phase G t) (k * t - t)).Reachable u v := by
    rw [← phase_add, Nat.add_sub_of_le ht]
    exact hz
  exact phase_reachable he

def Short (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v : V⦄, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w

theorem meta_two_of_short {J : SimpleGraph V} (hs : Short (metamour J)) :
    metamour (metamour (metamour J)) = metamour J := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro h
    by_cases hh : (metamour J).Adj u v
    · exact hh
    · exact False.elim (h.2.1 ⟨h.1, hh, hs h.1 hh⟩)
  · intro h
    have hh := h
    obtain ⟨hne, _, w, hu, hv⟩ := h
    refine ⟨hne, fun h' => h'.2.1 hh, w, ?_, ?_⟩
    · exact ⟨hu.ne, fun hm => hm.2.1 hu, hs hu.ne (fun hm => hm.2.1 hu)⟩
    · exact ⟨hv.ne, fun hm => hm.2.1 hv, hs hv.ne (fun hm => hm.2.1 hv)⟩

theorem phase_predecessor {G : SimpleGraph V} {k : ℕ} (hk : 0 < k)
    (hr : phase G k = G) (t : ℕ) : ∃ J, phase G t = metamour J := by
  refine ⟨phase G (t + k - 1), ?_⟩
  rw [← phase_succ, show t + k - 1 + 1 = t + k by omega, phase_shift hr]

theorem phase_even_of_two {G : SimpleGraph V} (h : phase G 2 = G) (m : ℕ) :
    phase G (2 * m) = G := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, phase_shift h, ih]

theorem no_edges_of_odd_two {G : SimpleGraph V} {k : ℕ} (hk : Odd k)
    (hr : phase G k = G) (h2 : phase G 2 = G) {u v : V} (h : G.Adj u v) : False := by
  obtain ⟨m, hm⟩ := hk
  have he : k = 2 * m + 1 := by omega
  have hf : metamour G = G := by
    simpa only [he, phase_succ, phase_even_of_two h2] using hr
  have hh : (metamour G).Adj u v := by rw [hf]; exact h
  exact hh.2.1 h

theorem no_short_phase_of_odd_edge {G : SimpleGraph V} {k t : ℕ} (hk : Odd k)
    (hr : phase G k = G) (hs : Short (phase G t))
    {u v : V} (h : (phase G t).Adj u v) : False := by
  have hp : 0 < k := by obtain ⟨m, hm⟩ := hk; omega
  obtain ⟨J, hj⟩ := phase_predecessor hp hr t
  have h2 : phase (phase G t) 2 = phase G t := by
    rw [hj]
    exact meta_two_of_short (hj ▸ hs)
  exact no_edges_of_odd_two hk (phase_return hr t) h2 h

#print axioms meta_adj_iff_edist
#print axioms phase_preconnected
#print axioms no_short_phase_of_odd_edge

end Metamour
```

## MetaTriangle.lean

```lean
import MetaBase

namespace Metamour

variable {V : Type*}

def Triangle (G : SimpleGraph V) (a b c : V) : Prop :=
  G.Adj a b ∧ G.Adj a c ∧ G.Adj b c

def IndependentTriple (G : SimpleGraph V) (a b c : V) : Prop :=
  ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c

theorem triangle_next_independent {G : SimpleGraph V} {a b c : V}
    (h : Triangle G a b c) : IndependentTriple (metamour G) a b c :=
  ⟨fun e => e.2.1 h.1, fun e => e.2.1 h.2.1, fun e => e.2.1 h.2.2⟩

theorem triangle_obstruction {G : SimpleGraph V} (hc : G.Preconnected)
    {a b c : V} (h : Triangle G a b c)
    (hi : IndependentTriple (metamour G) a b c)
    (hj : IndependentTriple (metamour (metamour G)) a b c) : Short G := by
  have hab := h.1
  have hac := h.2.1
  have hbc := h.2.2
  let near (x : V) := G.Adj x a ∨ G.Adj x b ∨ G.Adj x c
  let good (x : V) := (G.Adj x a ∨ G.Adj x b) ∧
    (G.Adj x a ∨ G.Adj x c) ∧ (G.Adj x b ∨ G.Adj x c)
  have ga : good a := ⟨Or.inr hab, Or.inr hac, Or.inl hab⟩
  have gb : good b := ⟨Or.inl hab.symm, Or.inl hab.symm, Or.inr hbc⟩
  have gc : good c := ⟨Or.inl hac.symm, Or.inl hac.symm, Or.inl hbc.symm⟩
  have blocked {x s t : V} (hst : G.Adj s t) (hn : ¬ (metamour G).Adj s t)
      (hnn : ¬ (metamour (metamour G)).Adj s t)
      (hs : (metamour G).Adj x s) (ht : (metamour G).Adj x t) : False :=
    hnn ⟨hst.ne, hn, x, hs.symm, ht.symm⟩
  have gNear (x : V) (hx : near x) : good x := by
    by_cases ha : x = a
    · simpa [ha] using ga
    by_cases hb : x = b
    · simpa [hb] using gb
    by_cases hc' : x = c
    · simpa [hc'] using gc
    have ma (hn : ¬ G.Adj x a) : (metamour G).Adj x a := by
      rcases hx with e | e | e
      · exact (hn e).elim
      · exact ⟨ha, hn, b, e, hab⟩
      · exact ⟨ha, hn, c, e, hac⟩
    have mb (hn : ¬ G.Adj x b) : (metamour G).Adj x b := by
      rcases hx with e | e | e
      · exact ⟨hb, hn, a, e, hab.symm⟩
      · exact (hn e).elim
      · exact ⟨hb, hn, c, e, hbc⟩
    have mc (hn : ¬ G.Adj x c) : (metamour G).Adj x c := by
      rcases hx with e | e | e
      · exact ⟨hc', hn, a, e, hac.symm⟩
      · exact ⟨hc', hn, b, e, hbc.symm⟩
      · exact (hn e).elim
    classical
    refine ⟨?_, ?_, ?_⟩
    · by_contra hn
      push Not at hn
      exact blocked hab hi.1 hj.1 (ma hn.1) (mb hn.2)
    · by_contra hn
      push Not at hn
      exact blocked hac hi.2.1 hj.2.1 (ma hn.1) (mc hn.2)
    · by_contra hn
      push Not at hn
      exact blocked hbc hi.2.2 hj.2.2 (mb hn.1) (mc hn.2)
  have step {x y : V} (e : G.Adj x y) (hy : good y) : good x := by
    by_cases hn : near x
    · exact gNear x hn
    have ha : x ≠ a := fun he => hn (Or.inr (Or.inl (he.symm ▸ hab)))
    have hb : x ≠ b := fun he => hn (Or.inl (he.symm ▸ hab.symm))
    have hc' : x ≠ c := fun he => hn (Or.inl (he.symm ▸ hac.symm))
    have ma (hy' : G.Adj y a) : (metamour G).Adj x a :=
      ⟨ha, fun he => hn (Or.inl he), y, e, hy'.symm⟩
    have mb (hy' : G.Adj y b) : (metamour G).Adj x b :=
      ⟨hb, fun he => hn (Or.inr (Or.inl he)), y, e, hy'.symm⟩
    have mc (hy' : G.Adj y c) : (metamour G).Adj x c :=
      ⟨hc', fun he => hn (Or.inr (Or.inr he)), y, e, hy'.symm⟩
    exact False.elim (by
      rcases hy.1 with ya | yb
      · rcases hy.2.2 with yb | yc
        · exact blocked hab hi.1 hj.1 (ma ya) (mb yb)
        · exact blocked hac hi.2.1 hj.2.1 (ma ya) (mc yc)
      · rcases hy.2.1 with ya | yc
        · exact blocked hab hi.1 hj.1 (ma ya) (mb yb)
        · exact blocked hbc hi.2.2 hj.2.2 (mb yb) (mc yc))
  have along {x y : V} (p : G.Walk x y) : good y → good x := by
    induction p with
    | nil => exact id
    | cons e _ ih => exact fun hh => step e (ih hh)
  have allGood (x : V) : good x := (hc x a).elim fun p => along p ga
  intro u v _ _
  have hu := allGood u
  have hv := allGood v
  dsimp only [good] at hu hv
  rcases hu.1 with ua | ub
  · rcases hv.1 with va | vb
    · exact ⟨a, ua, va⟩
    · rcases hu.2.2 with ub | uc
      · exact ⟨b, ub, vb⟩
      · rcases hv.2.1 with va | vc
        · exact ⟨a, ua, va⟩
        · exact ⟨c, uc, vc⟩
  · rcases hv.1 with va | vb
    · rcases hu.2.1 with ua | uc
      · exact ⟨a, ua, va⟩
      · rcases hv.2.2 with vb | vc
        · exact ⟨b, ub, vb⟩
        · exact ⟨c, uc, vc⟩
    · exact ⟨b, ub, vb⟩

theorem equal_history_no_triangle {G : SimpleGraph V} {k : ℕ} (hk : Odd k)
    (hp : G.Preconnected) (hr : phase G k = G) {a b c : V}
    (hab : ∀ t, (phase G t).Adj a b ↔ (phase G t).Adj a c)
    (hbc : ∀ t, (phase G t).Adj a b ↔ (phase G t).Adj b c)
    (t : ℕ) (h : (phase G t).Adj a b) : False := by
  obtain ⟨m, hm⟩ := hk
  have hkp : 0 < k := by omega
  have step (i : ℕ) (hi : (phase G i).Adj a b) : (phase G (i + 2)).Adj a b := by
    by_contra hn
    have tri : Triangle (phase G i) a b c := ⟨hi, (hab i).mp hi, (hbc i).mp hi⟩
    have ind : IndependentTriple (phase G (i + 2)) a b c :=
      ⟨hn, fun e => hn ((hab (i + 2)).mpr e), fun e => hn ((hbc (i + 2)).mpr e)⟩
    have short := triangle_obstruction (phase_preconnected hp hkp hr i) tri
      (triangle_next_independent tri) ind
    exact no_short_phase_of_odd_edge ⟨m, hm⟩ hr short hi
  have all (j : ℕ) : (phase G (t + 2 * j)).Adj a b := by
    induction j with
    | zero => simpa using h
    | succ j ih =>
      rw [show t + 2 * (j + 1) = t + 2 * j + 2 by omega]
      exact step _ ih
  have hh := all (m + 1)
  rw [show t + 2 * (m + 1) = (t + 1) + k by omega, phase_shift hr] at hh
  exact hh.2.1 h

#print axioms triangle_obstruction
#print axioms equal_history_no_triangle

end Metamour
```

## MetaRamsey.lean

```lean
import Mathlib.Combinatorics.Pigeonhole

namespace Metamour

def triangleBound : ℕ → ℕ
  | 0 => 2
  | q + 1 => (q + 1) * (triangleBound q - 1) + 2

theorem triangleBound_pos (q : ℕ) : 0 < triangleBound q := by
  cases q <;> simp [triangleBound]

theorem ramsey_triangle {V C : Type*} (color : V → V → C)
    (s : Finset V) (colors : Finset C) (hc : triangleBound colors.card ≤ s.card)
    (maps : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → color x y ∈ colors) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ color a b = color a c ∧ color a b = color b c := by
  classical
  generalize hq : colors.card = q at hc
  induction q generalizing s colors with
  | zero =>
    have hs : 2 ≤ s.card := hc
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    have hsa := Finset.card_erase_of_mem ha
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (s.erase a).card)
    obtain ⟨hba, hbs⟩ := Finset.mem_erase.mp hb
    have he : colors = ∅ := Finset.card_eq_zero.mp hq
    have hm := maps a ha b hbs hba.symm
    rw [he] at hm
    exact (Finset.notMem_empty _ hm).elim
  | succ q ih =>
    have ht : colors.card * (triangleBound q - 1) + 2 ≤ s.card := by
      simpa only [hq, triangleBound] using hc
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    have hsplit : colors.card * (triangleBound q - 1) < (s.erase v).card := by
      rw [Finset.card_erase_of_mem hv]
      omega
    have hm : ∀ x ∈ s.erase v, color v x ∈ colors := by
      intro x hx
      obtain ⟨hxv, hxs⟩ := Finset.mem_erase.mp hx
      exact maps v hv x hxs hxv.symm
    obtain ⟨d, hd, hbin⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hm hsplit
    let bin := (s.erase v).filter (fun x => color v x = d)
    have hbin' : triangleBound q - 1 < bin.card := hbin
    have hcard : triangleBound q ≤ bin.card := by
      have := triangleBound_pos q
      omega
    have members {x} (hx : x ∈ bin) : x ≠ v ∧ x ∈ s ∧ color v x = d := by
      obtain ⟨hm', hcol⟩ := Finset.mem_filter.mp hx
      obtain ⟨hne, hs⟩ := Finset.mem_erase.mp hm'
      exact ⟨hne, hs, hcol⟩
    by_cases hclose : ∃ x ∈ bin, ∃ y ∈ bin, x ≠ y ∧ color x y = d
    · obtain ⟨x, hx, y, hy, hxy, he⟩ := hclose
      obtain ⟨hxv, hxs, hxd⟩ := members hx
      obtain ⟨hyv, hys, hyd⟩ := members hy
      exact ⟨v, hv, x, hxs, y, hys, hxv.symm, hyv.symm, hxy, hxd.trans hyd.symm,
        hxd.trans he.symm⟩
    · have nextMaps : ∀ x ∈ bin, ∀ y ∈ bin, x ≠ y → color x y ∈ colors.erase d := by
        intro x hx y hy hxy
        exact Finset.mem_erase.mpr
          ⟨fun eq => hclose ⟨x, hx, y, hy, hxy, eq⟩,
            maps x (members hx).2.1 y (members hy).2.1 hxy⟩
      have nextCard : (colors.erase d).card = q := by
        rw [Finset.card_erase_of_mem hd, hq]
        omega
      obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc, eab, ebc⟩ :=
        ih bin (colors.erase d) nextMaps nextCard hcard
      exact ⟨a, (members ha).2.1, b, (members hb).2.1, c, (members hc').2.1,
        hab, hac, hbc, eab, ebc⟩

#print axioms ramsey_triangle

end Metamour
```

## MetaDegree.lean

```lean
import MetaTriangle
import MetaRamsey
import Mathlib.Data.Fintype.Pi

namespace Metamour

variable {V : Type*}

noncomputable def history (G : SimpleGraph V) (k : ℕ) (u v : V) : Fin k → Bool := by
  classical
  exact fun i => decide ((phase G i.val).Adj u v)

theorem history_symm (G : SimpleGraph V) (k : ℕ) (u v : V) :
    history G k u v = history G k v u := by
  funext i
  classical
  simp only [history, decide_eq_decide]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem phase_mod {G : SimpleGraph V} {k : ℕ} (hr : phase G k = G) (t : ℕ) :
    phase G (t % k) = phase G t := by
  have hmul (n : ℕ) : phase G (t % k + k * n) = phase G (t % k) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, ← Nat.add_assoc, phase_shift hr, ih]
  have hh := hmul (t / k)
  rw [Nat.mod_add_div] at hh
  exact hh.symm

theorem history_eq_adj {G : SimpleGraph V} {k : ℕ} (hk : 0 < k)
    (hr : phase G k = G) {u v x y : V} (he : history G k u v = history G k x y) (t : ℕ) :
    (phase G t).Adj u v ↔ (phase G t).Adj x y := by
  classical
  have hi := congrFun he (⟨t % k, Nat.mod_lt t hk⟩ : Fin k)
  simp only [history, decide_eq_decide] at hi
  simpa only [phase_mod hr] using hi

noncomputable def neighbors [Fintype V] (G : SimpleGraph V) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj u)

@[simp] theorem mem_neighbors [Fintype V] {G : SimpleGraph V} {u v : V} :
    v ∈ neighbors G u ↔ G.Adj u v := by
  classical
  simp [neighbors]

def degreeBound (k : ℕ) : ℕ := triangleBound (2 ^ k) - 1

theorem odd_return_degree_bound [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hk : Odd k) (hc : G.Preconnected) (hr : phase G k = G) (u : V) :
    (neighbors G u).card ≤ degreeBound k := by
  classical
  by_contra! hlarge
  have hkp : 0 < k := by obtain ⟨m, hm⟩ := hk; omega
  let colors : Finset (Fin k → Bool) := Finset.univ
  have hcolors : colors.card = 2 ^ k := by simp [colors]
  have big : triangleBound colors.card ≤ (neighbors G u).card := by
    rw [hcolors]
    unfold degreeBound at hlarge
    omega
  obtain ⟨a, ha, b, hb, c, _, hab, _, _, eab, ebc⟩ :=
    ramsey_triangle (history G k) (neighbors G u) colors big (by simp [colors])
  have h₁ := history_eq_adj hkp hr eab
  have h₂ := history_eq_adj hkp hr ebc
  by_cases e : G.Adj a b
  · exact equal_history_no_triangle hk hc hr h₁ h₂ 0 e
  · have hm : (phase G 1).Adj a b :=
      ⟨hab, e, u, (mem_neighbors.mp ha).symm, (mem_neighbors.mp hb).symm⟩
    exact equal_history_no_triangle hk hc hr h₁ h₂ 1 hm

#print axioms history_symm
#print axioms odd_return_degree_bound

end Metamour
```

## MetaDiameter.lean

```lean
import MetaBase

namespace Metamour

variable {V : Type*} {G : SimpleGraph V}

theorem meta_adj_iff_dist (G : SimpleGraph V) (u v : V) :
    (metamour G).Adj u v ↔ G.dist u v = 2 := by
  rw [meta_adj_iff_edist]
  constructor
  · intro h
    simp [SimpleGraph.dist, h]
  · intro h
    have hr : G.Reachable u v := SimpleGraph.Reachable.of_dist_ne_zero (by omega)
    rw [← hr.coe_dist_eq_edist, h]
    rfl

theorem dist_le_add (hc : G.Preconnected) (u v w : V) :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  obtain ⟨p, hp⟩ := (hc u v).exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := (hc v w).exists_walk_length_eq_dist
  simpa only [SimpleGraph.Walk.length_append, hp, hq] using G.dist_le (p.append q)

theorem geodesic_split (hc : G.Preconnected) {u v : V} {n : ℕ} (hn : n ≤ G.dist u v) :
    ∃ w, G.dist u w = n ∧ G.dist w v = G.dist u v - n := by
  obtain ⟨p, hp⟩ := (hc u v).exists_walk_length_eq_dist
  have ha : G.dist u (p.getVert n) ≤ n := by
    simpa only [SimpleGraph.Walk.take_length, hp, inf_eq_left.mpr hn] using G.dist_le (p.take n)
  have hb : G.dist (p.getVert n) v ≤ G.dist u v - n := by
    simpa only [SimpleGraph.Walk.drop_length, hp] using G.dist_le (p.drop n)
  have hsum : G.dist u v ≤ G.dist u (p.getVert n) + G.dist (p.getVert n) v :=
    dist_le_add hc u (p.getVert n) v
  refine ⟨p.getVert n, le_antisymm ha ?_, le_antisymm hb ?_⟩ <;> omega

theorem edge_dist_le_pow (hc : G.Preconnected) (t : ℕ) {u v : V}
    (h : (phase G t).Adj u v) : G.dist u v ≤ 2 ^ t := by
  induction t generalizing u v with
  | zero =>
    exact le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr h)
  | succ t ih =>
    obtain ⟨_, _, w, hu, hv⟩ := h
    have ha := ih hu
    have hb := ih hv.symm
    have hsum := dist_le_add hc u w v
    rw [pow_succ]
    omega

theorem edge_of_dyadic_dist (hc : G.Preconnected) (t : ℕ) {u v : V}
    (h : G.dist u v = 2 ^ t) : (phase G t).Adj u v := by
  induction t generalizing u v with
  | zero => exact SimpleGraph.dist_eq_one_iff_adj.mp h
  | succ t ih =>
    have he : 2 ^ t ≤ G.dist u v := by rw [h, pow_succ]; omega
    obtain ⟨w, hw, hw'⟩ := geodesic_split hc he
    have hmid : G.dist v w = 2 ^ t := by
      rw [SimpleGraph.dist_comm (u := v) (v := w), hw', h, pow_succ]
      omega
    have hpos : 0 < (2 : ℕ) ^ t := pow_pos (by decide) _
    refine ⟨?_, ?_, w, ih hw, ih hmid⟩
    · intro huv
      subst v
      rw [SimpleGraph.dist_self, pow_succ] at h
      omega
    · intro hn
      have hle := edge_dist_le_pow hc t hn
      rw [h, pow_succ] at hle
      omega

theorem return_diameter_bound (hc : G.Preconnected) {k : ℕ} (hk : 0 < k)
    (hr : phase G k = G) (u v : V) : G.dist u v < 2 ^ k := by
  by_contra! h
  obtain ⟨w, hw, _⟩ := geodesic_split hc h
  have he := edge_of_dyadic_dist hc k hw
  rw [hr] at he
  have hd := SimpleGraph.dist_eq_one_iff_adj.mpr he
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [hd, pow_succ] at hw
  have hp : 0 < (2 : ℕ) ^ j := pow_pos (by decide) _
  omega

#print axioms meta_adj_iff_dist
#print axioms geodesic_split
#print axioms edge_dist_le_pow
#print axioms edge_of_dyadic_dist
#print axioms return_diameter_bound

end Metamour
```

## MetaOrder.lean

```lean
import MetaDegree
import MetaDiameter
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Metamour

variable {V : Type*} {G : SimpleGraph V}

noncomputable def ball [Fintype V] (G : SimpleGraph V) : ℕ → V → Finset V := by
  classical
  exact Nat.rec (fun u => {u})
    (fun _ previous u => {u} ∪ (neighbors G u).biUnion previous)

theorem mem_ball_of_walk [Fintype V] {u v : V} (p : G.Walk u v) {n : ℕ}
    (h : p.length ≤ n) : v ∈ ball G n u := by
  classical
  induction p generalizing n with
  | nil =>
    cases n <;> simp [ball]
  | cons e p ih =>
    cases n with
    | zero =>
      simp at h
    | succ n =>
      simp only [SimpleGraph.Walk.length_cons] at h
      simp only [ball, Finset.mem_union, Finset.mem_biUnion]
      exact Or.inr ⟨_, mem_neighbors.mpr e, ih (by omega)⟩

def ballBound (D : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => 1 + D * ballBound D n

theorem ball_card_bound [Fintype V] {D : ℕ} (hd : ∀ u, (neighbors G u).card ≤ D)
    (n : ℕ) (u : V) : (ball G n u).card ≤ ballBound D n := by
  classical
  induction n generalizing u with
  | zero => simp [ball, ballBound]
  | succ n ih =>
    have hcount := Finset.card_biUnion_le_card_mul (neighbors G u) (ball G n)
      (ballBound D n) (fun v _ => ih v)
    calc
      (ball G (n+1) u).card ≤ 1 + ((neighbors G u).biUnion (ball G n)).card := by
        simpa [ball] using Finset.card_union_le ({u} : Finset V)
          ((neighbors G u).biUnion (ball G n))
      _ ≤ 1 + (neighbors G u).card * ballBound D n := Nat.add_le_add_left hcount 1
      _ ≤ ballBound D (n+1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ (hd u)) 1

def orderBound (k : ℕ) : ℕ := ballBound (degreeBound k) (2 ^ k - 1)

theorem odd_return_order_bound [Fintype V] {k : ℕ} (hk : Odd k) (hc : G.Preconnected)
    (hr : phase G k = G) : Fintype.card V ≤ orderBound k := by
  classical
  by_cases h : Nonempty V
  · obtain ⟨u⟩ := h
    have hkp : 0 < k := by obtain ⟨m, hm⟩ := hk; omega
    have hb : ball G (2 ^ k - 1) u = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      obtain ⟨p, hp⟩ := (hc u v).exists_walk_length_eq_dist
      have hdist := return_diameter_bound hc hkp hr u v
      exact mem_ball_of_walk p (by omega)
    have count := ball_card_bound (fun v => odd_return_degree_bound hk hc hr v)
      (2 ^ k - 1) u
    simpa only [hb, Finset.card_univ, orderBound] using count
  · let : IsEmpty V := not_nonempty_iff.mp h
    simp

#print axioms mem_ball_of_walk
#print axioms ball_card_bound
#print axioms odd_return_order_bound

end Metamour
```

## MetaFiniteness.lean

```lean
import MetaOrder
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma

namespace Metamour

universe u v

variable {V : Type u} {W : Type v}

theorem metamour_comap (e : V ≃ W) (G : SimpleGraph W) :
    metamour (G.comap e) = (metamour G).comap e := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  constructor
  · rintro ⟨hne, hna, z, hx, hy⟩
    exact ⟨fun hh => hne (e.injective hh), hna, e z, hx, hy⟩
  · rintro ⟨hne, hna, z, hx, hy⟩
    refine ⟨fun hh => hne (congrArg e hh), hna, e.symm z, ?_, ?_⟩
    · simpa only [SimpleGraph.comap_adj, e.apply_symm_apply] using hx
    · simpa only [SimpleGraph.comap_adj, e.apply_symm_apply] using hy

theorem phase_comap (e : V ≃ W) (G : SimpleGraph W) (n : ℕ) :
    phase (G.comap e) n = (phase G n).comap e := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [phase_succ, ih, metamour_comap]

theorem comap_injective (e : V ≃ W) :
    Function.Injective (fun G : SimpleGraph W => G.comap e) := by
  intro G H hh
  apply SimpleGraph.ext
  funext x y
  have h := congrFun (congrFun (congrArg SimpleGraph.Adj hh) (e.symm x)) (e.symm y)
  change G.Adj (e (e.symm x)) (e (e.symm y)) = H.Adj (e (e.symm x)) (e (e.symm y)) at h
  simpa only [e.apply_symm_apply] using h

theorem exactPeriod_comap_iff (e : V ≃ W) (G : SimpleGraph W) (k : ℕ) :
    ExactPeriod (G.comap e) k ↔ ExactPeriod G k := by
  have hr (j : ℕ) : phase (G.comap e) j = G.comap e ↔ phase G j = G := by
    rw [phase_comap]
    exact (comap_injective e).eq_iff
  exact ⟨fun ⟨hk, h, hm⟩ => ⟨hk, (hr k).mp h,
    fun j hj hlt hjr => hm j hj hlt ((hr j).mpr hjr)⟩,
    fun ⟨hk, h, hm⟩ => ⟨hk, (hr k).mpr h,
    fun j hj hlt hjr => hm j hj hlt ((hr j).mp hjr)⟩⟩

theorem exactPeriod_iso_iff {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (k : ℕ) : ExactPeriod G k ↔ ExactPeriod H k := by
  have hh : H.comap e.toEquiv = G := by
    apply SimpleGraph.ext
    funext x y
    exact propext e.map_rel_iff
  rw [← hh, exactPeriod_comap_iff]

private noncomputable def candidates (B : ℕ) : Finset (Σ n : ℕ, SimpleGraph (Fin n)) := by
  classical
  let source : Finset (Σ i : Fin (B + 1), SimpleGraph (Fin i.val)) := Finset.univ
  exact source.image (fun s => ⟨s.1.val, s.2⟩)

private theorem mem_candidates {B n : ℕ} (hn : n ≤ B) (H : SimpleGraph (Fin n)) :
    (⟨n, H⟩ : Σ j : ℕ, SimpleGraph (Fin j)) ∈ candidates B := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨⟨⟨n, by omega⟩, H⟩, Finset.mem_univ _, rfl⟩

theorem finite_exact_odd_period_preconnected (k : ℕ) (hk : Odd k) :
    ∃ S : Finset (Σ n : ℕ, SimpleGraph (Fin n)),
      (∀ s ∈ S, s.2.Preconnected ∧ ExactPeriod s.2 k) ∧
      ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
        G.Preconnected → ExactPeriod G k →
        ∃ s ∈ S, Nonempty (G ≃g s.2) := by
  classical
  let S := (candidates (orderBound k)).filter (fun s => s.2.Preconnected ∧ ExactPeriod s.2 k)
  refine ⟨S, fun s hs => (Finset.mem_filter.mp hs).2, ?_⟩
  intro V inst G hc hp
  let := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let H := G.comap e.symm
  let iso : G ≃g H := (SimpleGraph.Iso.comap e.symm G).symm
  have hm : Fintype.card V ≤ orderBound k := odd_return_order_bound hk hc hp.2.1
  have hH : H.Preconnected := hc.map iso.toHom iso.surjective
  have hP : ExactPeriod H k := (exactPeriod_iso_iff iso k).mp hp
  exact ⟨⟨Fintype.card V, H⟩, Finset.mem_filter.mpr ⟨mem_candidates hm H, hH, hP⟩, ⟨iso⟩⟩

theorem finite_exact_odd_period (k : ℕ) (hk : Odd k) :
    ∃ S : Finset (Σ n : ℕ, SimpleGraph (Fin n)),
      (∀ s ∈ S, s.2.Connected ∧ ExactPeriod s.2 k) ∧
      ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
        G.Connected → ExactPeriod G k →
        ∃ s ∈ S, Nonempty (G ≃g s.2) := by
  classical
  obtain ⟨S, hs, hcover⟩ := finite_exact_odd_period_preconnected.{u} k hk
  refine ⟨S.filter (fun s => s.2.Connected), ?_, ?_⟩
  · intro s hm
    obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hm
    exact ⟨hc, (hs s hmem).2⟩
  · intro V inst G hc hp
    obtain ⟨s, hm, ⟨iso⟩⟩ := hcover G hc.preconnected hp
    exact ⟨s, Finset.mem_filter.mpr ⟨hm, hc.map iso.toHom iso.surjective⟩, ⟨iso⟩⟩

#print axioms exactPeriod_iso_iff
#print axioms finite_exact_odd_period_preconnected
#print axioms finite_exact_odd_period

end Metamour
```

## MetaScope.lean

```lean
import MetaFiniteness
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Metamour

variable {V : Type*} {G : SimpleGraph V}

theorem phase_connected (hc : G.Connected) {k : ℕ} (hk : 0 < k)
    (hr : phase G k = G) (t : ℕ) : (phase G t).Connected where
  preconnected := phase_preconnected hc.preconnected hk hr t
  nonempty := hc.nonempty

theorem short_iff_ediam_le_two : Short G ↔ G.ediam ≤ 2 := by
  rw [SimpleGraph.ediam_le_iff]
  constructor
  · intro hs u v
    by_contra! h
    have ⟨hne, hn, hnone⟩ := SimpleGraph.two_lt_edist_iff.mp h
    have hw : (G.commonNeighbors u v).Nonempty := hs hne hn
    rw [hnone] at hw
    exact Set.not_nonempty_empty hw
  · intro hs u v hne hn
    change (G.commonNeighbors u v).Nonempty
    by_contra hempty
    have hnone : G.commonNeighbors u v = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    exact (not_lt_of_ge (hs u v)) (SimpleGraph.two_lt_edist_iff.mpr ⟨hne, hn, hnone⟩)

theorem return_ediam_bound (hc : G.Preconnected) {k : ℕ} (hk : 0 < k)
    (hr : phase G k = G) : G.ediam ≤ ((2 ^ k - 1 : ℕ) : ℕ∞) := by
  apply SimpleGraph.ediam_le_of_edist_le
  intro u v
  rw [← (hc u v).coe_dist_eq_edist]
  exact_mod_cast Nat.le_sub_one_of_lt (return_diameter_bound hc hk hr u v)

theorem odd_return_degree_bound_native [Fintype V] {k : ℕ} (hk : Odd k)
    (hc : G.Preconnected) (hr : phase G k = G) (u : V) [Fintype (G.neighborSet u)] :
    G.degree u ≤ degreeBound k := by
  have hh : neighbors G u = G.neighborFinset u := by
    ext v
    simp
  rw [← G.card_neighborFinset_eq_degree, ← hh]
  exact odd_return_degree_bound hk hc hr u

theorem exactPeriod_one_iff_subsingleton (hc : G.Preconnected) :
    ExactPeriod G 1 ↔ Subsingleton V := by
  constructor
  · intro h
    have hf : metamour G = G := h.2.1
    have noEdge {u v : V} (e : G.Adj u v) : False := by
      have e' : (metamour G).Adj u v := by rwa [hf]
      exact e'.2.1 e
    refine ⟨fun u v => ?_⟩
    obtain ⟨p⟩ := hc u v
    cases p with
    | nil => rfl
    | cons e _ => exact (noEdge e).elim
  · intro hs
    refine ⟨by decide, ?_, fun j hj hj' => by omega⟩
    change metamour G = G
    apply SimpleGraph.ext
    funext u v
    apply propext
    have he := hs.elim u v
    subst v
    exact ⟨fun h => (h.1 rfl).elim, fun h => (h.ne rfl).elim⟩

theorem exactPeriod_subsingleton_iff [Subsingleton V] (k : ℕ) :
    ExactPeriod G k ↔ k = 1 := by
  have hc : G.Preconnected := fun u v => Subsingleton.elim u v ▸ .refl u
  have h1 := (exactPeriod_one_iff_subsingleton hc).mpr (inferInstance : Subsingleton V)
  constructor
  · intro h
    by_contra hn
    exact h.2.2 1 (by decide) (by have := h.1; omega) h1.2.1
  · rintro rfl
    exact h1

#print axioms phase_connected
#print axioms short_iff_ediam_le_two
#print axioms return_ediam_bound
#print axioms odd_return_degree_bound_native
#print axioms exactPeriod_one_iff_subsingleton
#print axioms exactPeriod_subsingleton_iff

end Metamour
```

