import CrownVGraph
import CrownVCount

/-!
Side structure of the crown graph: side counting, the side-swap symmetry,
path-transfer lemmas, the closure principle, and survivor-index existence.
`vidx`/`isX` and `cadj` are defined in `CrownVGraph`.
-/

namespace CrownV

variable {n : ℕ}

/-- Double Boolean negation. -/
theorem bnot2 (b : Bool) : (!(!b)) = b := by cases b <;> rfl

/-- `!b = true` means `b = false`. -/
theorem bnot_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | true => rw [Bool.not_true] at h; exact h.symm
  | false => rfl

/-- Number of X-side vertices in `s`. -/
abbrev xcnt (s : Finset (V n)) : ℕ := (Finset.filter (fun v : V n => (isX v)) s).card

/-- Number of Y-side vertices in `s`. -/
abbrev ycnt (s : Finset (V n)) : ℕ := (Finset.filter (fun v : V n => (isX v).not) s).card

/-- An X-side vertex is some `a k`. -/
theorem inl_of_isX {y : V n} (h : isX y = true) : ∃ k : Fin n, y = Sum.inl k := inl_of_sideX h

/-- A Y-side vertex is some `b k`. -/
theorem inr_of_isY {y : V n} (h : isX y = false) : ∃ k : Fin n, y = Sum.inr k := inr_of_sideY h

/-- Opposite sides as a Bool condition. -/
theorem not_sides {a b : Bool} (h : a ≠ b) :
    ((!a = true ∧ !b = false) ∨ (!a = false ∧ !b = true)) := by
  cases a with
  | true => cases b with
    | true => exact absurd rfl h
    | false => exact Or.inr ⟨rfl, rfl⟩
  | false => cases b with
    | true => exact Or.inl ⟨rfl, rfl⟩
    | false => exact absurd rfl h

/-- The cross edge from `a i` to a Y-side vertex of unequal index. -/
theorem cadj_to_Y {i : Fin n} {y : V n} (hy : isX y = false) (hne : i ≠ vidx y) :
    cadj (Sum.inl i) y := by
  obtain ⟨k, rfl⟩ := inr_of_isY hy
  rw [vidx_inr] at hne
  exact cadj_inl_inr.2 hne

/-- Side swap. -/
def vswap : V n → V n
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

@[simp] theorem vswap_inl (i : Fin n) : vswap (Sum.inl i) = Sum.inr i := rfl

@[simp] theorem vswap_inr (i : Fin n) : vswap (Sum.inr i) = Sum.inl i := rfl

@[simp] theorem vswap_vswap (v : V n) : vswap (vswap v) = v := by cases v <;> simp [vswap]

theorem vswap_inj : Function.Injective (vswap (n := n)) := by
  intro a b h
  calc a = vswap (vswap a) := (vswap_vswap a).symm
    _ = vswap (vswap b) := by rw [h]
    _ = b := vswap_vswap b

theorem vidx_vswap (v : V n) : vidx (vswap v) = vidx v := by cases v <;> simp [vswap, vidx]

theorem isX_vswap (v : V n) : isX (vswap v) = (isX v).not := by cases v <;> simp [vswap, isX]

/-- Edges are preserved by the side swap. -/
theorem cadj_vswap {u v : V n} (h : cadj u v) : cadj (vswap u) (vswap v) := by
  refine ⟨?_, ?_⟩
  · rw [vidx_vswap, vidx_vswap]; exact h.1
  · rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : isX u = true := h1
      have h2' : isX v = false := h2
      refine Or.inr ⟨?_, ?_⟩
      · show isX (vswap u) = false; rw [isX_vswap, h1']; rfl
      · show isX (vswap v) = true; rw [isX_vswap, h2']; rfl
    · have h1' : isX u = false := h1
      have h2' : isX v = true := h2
      refine Or.inl ⟨?_, ?_⟩
      · show isX (vswap u) = true; rw [isX_vswap, h1']; rfl
      · show isX (vswap v) = false; rw [isX_vswap, h2']; rfl

theorem sEdge_vswap {s : Finset (V n)} {x y : V n} (h : SEdge s x y) :
    SEdge (s.image vswap) (vswap x) (vswap y) :=
  ⟨Finset.mem_image.2 ⟨x, h.1, rfl⟩, Finset.mem_image.2 ⟨y, h.2.1, rfl⟩, cadj_vswap h.2.2⟩

/-- Paths transfer along any map that sends edges to edges. -/
theorem sameC_map {s t : Finset (V n)} {f : V n → V n}
    (hE : ∀ x y : V n, SEdge s x y → SEdge t (f x) (f y)) {x y : V n} (h : SameC s x y) :
    SameC t (f x) (f y) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact SameC.trans' ih (SameC.single (hE _ _ hstep))

theorem sameC_vswap {s : Finset (V n)} {x y : V n} (h : SameC s x y) :
    SameC (s.image vswap) (vswap x) (vswap y) :=
  sameC_map (fun _ _ hE => sEdge_vswap hE) h

/-- Paths only grow with the ambient set. -/
theorem sameC_congr_set {s t : Finset (V n)} (hst : s ⊆ t) {x y : V n} (h : SameC s x y) :
    SameC t x y := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    refine SameC.trans' ih (SameC.single ⟨hst hstep.1, hst hstep.2.1, hstep.2.2⟩)

theorem sameC_vswap_inv {s : Finset (V n)} {x y : V n}
    (h : SameC (s.image vswap) x y) : SameC s (vswap x) (vswap y) := by
  have h2 : SameC (Finset.image vswap (s.image vswap)) (vswap x) (vswap y) :=
    sameC_vswap h
  have hsub : Finset.image vswap (Finset.image vswap s) ⊆ s := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.1 hz
    obtain ⟨u, hu, hwu⟩ := Finset.mem_image.1 hw
    have e1 : z = vswap w := hwz.symm
    have e2 : w = vswap u := hwu.symm
    rw [e1, e2, vswap_vswap]
    exact hu
  exact sameC_congr_set hsub h2

theorem xcnt_vswap (s : Finset (V n)) : xcnt (s.image vswap) = ycnt s := by
  have hfil : Finset.image vswap (Finset.filter (fun v : V n => (isX v).not) s)
      = Finset.filter (fun v : V n => (isX v)) (Finset.image vswap s) := by
    ext v
    constructor
    · intro h
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨hws, hwX⟩ := Finset.mem_filter.1 hw
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨w, hws, rfl⟩, ?_⟩
      rw [isX_vswap]; exact hwX
    · intro h
      obtain ⟨himg, hv⟩ := Finset.mem_filter.1 h
      obtain ⟨w, hws, rfl⟩ := Finset.mem_image.1 himg
      refine Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hws, ?_⟩, rfl⟩
      rw [isX_vswap] at hv; exact hv
  calc xcnt (Finset.image vswap s)
      = (Finset.filter (fun v : V n => (isX v)) (Finset.image vswap s)).card := rfl
    _ = (Finset.image vswap (Finset.filter (fun v : V n => (isX v).not) s)).card := by
        rw [hfil]
    _ = (Finset.filter (fun v : V n => (isX v).not) s).card :=
        Finset.card_image_of_injOn (fun a _ b _ h => vswap_inj h)
    _ = ycnt s := rfl

theorem ycnt_vswap (s : Finset (V n)) : ycnt (s.image vswap) = xcnt s := by
  have hfil : Finset.image vswap (Finset.filter (fun v : V n => (isX v)) s)
      = Finset.filter (fun v : V n => (isX v).not) (Finset.image vswap s) := by
    ext v
    constructor
    · intro h
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨hws, hwX⟩ := Finset.mem_filter.1 hw
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨w, hws, rfl⟩, ?_⟩
      rw [isX_vswap, hwX]; rfl
    · intro h
      obtain ⟨himg, hv⟩ := Finset.mem_filter.1 h
      obtain ⟨w, hws, rfl⟩ := Finset.mem_image.1 himg
      refine Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hws, ?_⟩, rfl⟩
      have hwX : isX w = true := by
        rw [isX_vswap] at hv
        rw [bnot2] at hv
        exact hv
      exact hwX
  calc ycnt (Finset.image vswap s)
      = (Finset.filter (fun v : V n => (isX v).not) (Finset.image vswap s)).card := rfl
    _ = (Finset.image vswap (Finset.filter (fun v : V n => (isX v)) s)).card := by
        rw [hfil]
    _ = (Finset.filter (fun v : V n => (isX v)) s).card :=
        Finset.card_image_of_injOn (fun a _ b _ h => vswap_inj h)
    _ = xcnt s := rfl

/-- Closure principle: a subset of `s` closed under crown-neighbors in `s`
contains the whole `s`-component of each of its points. -/
theorem sameC_mem_of_closed {s D : Finset (V n)} {x : V n}
    (hx : x ∈ D) (hcl : ∀ a ∈ D, ∀ b ∈ s, cadj a b → b ∈ D) :
    ∀ y, SameC s x y → y ∈ D := by
  intro y h
  induction h with
  | refl => exact hx
  | tail _ hstep ih => exact hcl _ ih _ hstep.2.1 hstep.2.2

theorem SameC.two {s : Finset (V n)} {x m y : V n}
    (h1 : SEdge s x m) (h2 : SEdge s m y) : SameC s x y :=
  SameC.trans' (SameC.single h1) (SameC.single h2)

theorem SameC.chain3 {s : Finset (V n)} {a b c d : V n}
    (h1 : SEdge s a b) (h2 : SEdge s b c) (h3 : SEdge s c d) : SameC s a d :=
  (SameC.two h1 h2).trans' (SameC.single h3)

theorem SameC.chain4 {s : Finset (V n)} {a b c d e : V n}
    (h1 : SEdge s a b) (h2 : SEdge s b c) (h3 : SEdge s c d) (h4 : SEdge s d e) :
    SameC s a e :=
  (SameC.two h1 h2).trans' (SameC.two h3 h4)

/-- An X-side survivor with index avoiding two given indices exists whenever
at least three X-side vertices survive. -/
theorem exists_x_idx_ne {s : Finset (V n)} (h3 : 3 ≤ xcnt s) (a b : Fin n) :
    ∃ x ∈ s, isX x = true ∧ vidx x ≠ a ∧ vidx x ≠ b := by
  by_contra hex
  have hex' : ∀ x ∈ s, isX x = true → vidx x = a ∨ vidx x = b := by
    intro x hx hxX
    by_cases h1 : vidx x = a
    · exact Or.inl h1
    · by_cases h2 : vidx x = b
      · exact Or.inr h2
      · exact absurd ⟨x, hx, hxX, h1, h2⟩ hex
  have hsub : Finset.filter (fun v : V n => (isX v)) s ⊆
      Finset.image (fun k : Fin n => Sum.inl k) ({a, b} : Finset (Fin n)) := by
    intro v hv
    obtain ⟨hvs, hx⟩ := Finset.mem_filter.1 hv
    obtain ⟨k, rfl⟩ := inl_of_isX hx
    rcases hex' (Sum.inl k) hvs hx with h | h
    · rw [vidx_inl] at h; rw [h]
      exact Finset.mem_image.2 ⟨a, by simp, rfl⟩
    · rw [vidx_inl] at h; rw [h]
      exact Finset.mem_image.2 ⟨b, by simp, rfl⟩
  have hc : xcnt s ≤ 2 := by
    refine (Finset.card_le_card hsub).trans ?_
    refine Finset.card_image_le.trans ?_
    by_cases hab : a = b
    · subst hab; simp
    · have hna : a ∉ ({b} : Finset (Fin n)) := by
        intro h
        rw [Finset.mem_singleton] at h
        exact hab h
      rw [Finset.card_insert_of_notMem hna]
      simp
  omega

/-- A Y-side survivor with index avoiding a given one exists whenever at least
two Y-side vertices survive. -/
theorem exists_y_idx_ne {s : Finset (V n)} (h2 : 2 ≤ ycnt s) (a : Fin n) :
    ∃ y ∈ s, isX y = false ∧ vidx y ≠ a := by
  by_contra hex
  have hex' : ∀ y ∈ s, isX y = false → vidx y = a := by
    intro y hy hyY
    by_cases h1 : vidx y = a
    · exact h1
    · exact absurd ⟨y, hy, hyY, h1⟩ hex
  have hsub : Finset.filter (fun v : V n => (isX v).not) s ⊆
      Finset.image (fun k : Fin n => Sum.inr k) ({a} : Finset (Fin n)) := by
    intro v hv
    obtain ⟨hvs, hy⟩ := Finset.mem_filter.1 hv
    have hyF : isX v = false := bnot_true hy
    obtain ⟨k, rfl⟩ := inr_of_isY hyF
    have hk := hex' (Sum.inr k) hvs hyF
    rw [vidx_inr] at hk; rw [hk]
    exact Finset.mem_image.2 ⟨a, by simp, rfl⟩
  have hc : ycnt s ≤ 1 := by
    refine (Finset.card_le_card hsub).trans ?_
    refine Finset.card_image_le.trans ?_
    simp
  omega

end CrownV
