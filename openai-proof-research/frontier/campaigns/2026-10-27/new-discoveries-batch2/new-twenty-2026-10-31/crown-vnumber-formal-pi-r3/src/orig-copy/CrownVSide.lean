import CrownVGraph
import CrownVCount

/-!
Side structure of the crown graph: the index function, the side test, the
side-swap symmetry, path-building lemmas, the closure principle, and the
connectivity classification for induced subgraphs with enough survivors.
-/

namespace CrownV

variable {n : ℕ}

/-- The index of a vertex, on either side. -/
def vidx : V n → Fin n
  | Sum.inl i => i
  | Sum.inr i => i

/-- Whether the vertex lies on the X side (`a i`). -/
def isX : V n → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- Number of X-side vertices in `s`. -/
abbrev xcnt (s : Finset (V n)) : ℕ := (Finset.filter (fun v => isX v) s).card

/-- Number of Y-side vertices in `s`. -/
abbrev ycnt (s : Finset (V n)) : ℕ := (Finset.filter (fun v => (isX v).not) s).card

theorem isX_inl {i : Fin n} : isX (Sum.inl i) = true := rfl

theorem isX_inr {i : Fin n} : isX (Sum.inr i) = false := rfl

/-- `p.not = true` means `p = false`. -/
theorem eq_false_of_bnot {p : Bool} (h : p.not = true) : p = false := by
  cases p with
  | true => rw [Bool.not_true] at h; exact h.symm
  | false => rfl

/-- `p.not = false` means `p = true`. -/
theorem eq_true_of_bnot {p : Bool} (h : p.not = false) : p = true := by
  cases p with
  | true => rfl
  | false => rw [Bool.not_false] at h; exact h.symm

theorem vidx_inl {i : Fin n} : vidx (Sum.inl i) = i := rfl

theorem vidx_inr {i : Fin n} : vidx (Sum.inr i) = i := rfl

/-- An X-side vertex is some `a k`. -/
theorem isX_to_inl {y : V n} (h : isX y = true) : ∃ k : Fin n, y = Sum.inl k := by
  cases y with
  | inl k => exact ⟨k, rfl⟩
  | inr k => rw [isX_inr] at h; exact absurd h (by decide)

theorem isY_to_inr {y : V n} (h : isX y = false) : ∃ k : Fin n, y = Sum.inr k := by
  cases y with
  | inl k => rw [isX_inl] at h; exact absurd h (by decide)
  | inr k => exact ⟨k, rfl⟩

theorem cadj_inl_inr {i j : Fin n} : cadj (Sum.inl i) (Sum.inr j) = (i ≠ j) := rfl

theorem cadj_inr_inl {i j : Fin n} : cadj (Sum.inr i) (Sum.inl j) = (i ≠ j) := rfl

/-- The cross edge from a fixed X index to a Y-side vertex. -/
theorem cadj_to_Y {i : Fin n} {y : V n} (hy : isX y = false) (hne : i ≠ vidx y) :
    cadj (Sum.inl i) y := by
  obtain ⟨k, rfl⟩ := isY_to_inr hy
  rw [vidx_inr] at hne
  rw [cadj_inl_inr]
  exact hne

/-- Side swap. -/
def vswap : V n → V n
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

@[simp] theorem vswap_vswap (v : V n) : vswap (vswap v) = v := by cases v <;> rfl

theorem vswap_inj : Function.Injective (vswap (n := n)) := fun a b h =>
  congrArg vswap (by simpa using h)

theorem isX_vswap (v : V n) : isX (vswap v) = (isX v).not := by cases v <;> rfl

theorem cadj_vswap {u v : V n} : cadj (vswap u) (vswap v) ↔ cadj u v := by
  cases u <;> cases v <;> simp [vswap, cadj, isX, vidx] <;> tauto

theorem sEdge_vswap {s : Finset (V n)} {x y : V n} (h : SEdge s x y) :
    SEdge (s.image vswap) (vswap x) (vswap y) :=
  ⟨Finset.mem_image.2 ⟨x, h.1, rfl⟩, Finset.mem_image.2 ⟨y, h.2.1, rfl⟩,
    cadj_vswap.2 h.2.2⟩

/-- Paths transfer along any map that sends edges to edges. -/
theorem sameC_map {s t : Finset (V n)} {f : V n → V n}
    (hE : ∀ x y : V n, SEdge s x y → SEdge t (f x) (f y)) {x y : V n} (h : SameC s x y) :
    SameC t (f x) (f y) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    exact SameC.trans' ih (SameC.single (hE _ _ hstep))

theorem sameC_vswap {s : Finset (V n)} {x y : V n} (h : SameC s x y) :
    SameC (s.image vswap) (vswap x) (vswap y) :=
  sameC_map (fun _ _ hE => sEdge_vswap hE) h

/-- Paths only depend on the edge relation visible in the ambient set. -/
theorem sameC_congr_set {s t : Finset (V n)} (hst : s ⊆ t) {x y : V n} (h : SameC s x y) :
    SameC t x y := by
  -- transfer along the inclusion map
  exact sameC_map (fun _ hE => (⟨hst hE.1, hst hE.2.1, hE.2.2⟩ : SEdge t _ _)) h

theorem sameC_vswap_inv {s : Finset (V n)} {x y : V n}
    (h : SameC (s.image vswap) x y) : SameC s (vswap x) (vswap y) := by
  have h2 : SameC (Finset.image vswap (s.image vswap)) (vswap x) (vswap y) :=
    sameC_vswap h
  have hsub : Finset.image vswap (Finset.image vswap (n := n) s) ⊆ s := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨w', _, rfl⟩ := Finset.mem_image.1 hw
    rw [vswap_vswap]
    exact hw'
  exact sameC_congr_set hsub h2

theorem xcnt_vswap (s : Finset (V n)) : xcnt (s.image vswap) = ycnt s := by
  have hfil : Finset.filter (fun v : V n => isX v) (s.image vswap)
      = Finset.image vswap (Finset.filter (fun v : V n => (isX v).not) s) := by
    ext v
    constructor
    · rintro ⟨hmem, hx⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hmem
      rw [isX_vswap] at hx
      exact ⟨w, Finset.mem_filter.2 ⟨hw, hx, rfl⟩, rfl⟩
    · rintro ⟨w, hmem, rfl⟩
      obtain ⟨hw, hp⟩ := Finset.mem_filter.1 hmem
      refine ⟨Finset.mem_image.2 ⟨w, hw, rfl⟩, ?_⟩
      rw [isX_vswap, hp]
  rw [hfil, Finset.card_image_of_injOn (fun a _ b _ h => vswap_inj h)]

theorem ycnt_vswap (s : Finset (V n)) : ycnt (s.image vswap) = xcnt s := by
  have hfil : Finset.filter (fun v : V n => (isX v).not) (s.image vswap)
      = Finset.image vswap (Finset.filter (fun v : V n => isX v) s) := by
    ext v
    constructor
    · rintro ⟨hmem, hx⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hmem
      rw [isX_vswap] at hx
      rw [hx]
      exact ⟨w, Finset.mem_filter.2 ⟨hw, rfl, rfl⟩, rfl⟩
    · rintro ⟨w, hmem, rfl⟩
      obtain ⟨hw, hx⟩ := Finset.mem_filter.1 hmem
      refine ⟨Finset.mem_image.2 ⟨w, hw, rfl⟩, ?_⟩
      rw [isX_vswap, hx]
  rw [hfil, Finset.card_image_of_injOn (fun a _ b _ h => vswap_inj h)]

/-- Closure principle: if every crown-neighbor in `s` of a point of `D` again
lies in `D`, then `D` contains the whole `s`-component of any of its points. -/
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

/-- An X-side survivor whose index avoids two given indices, from at least
three X-side survivors. -/
theorem exists_x_idx_ne {s : Finset (V n)} (h3 : 3 ≤ xcnt s) (a b : Fin n) :
    ∃ x ∈ s, isX x = true ∧ vidx x ≠ a ∧ vidx x ≠ b := by
  by_contra hex
  have hex' : ∀ x ∈ s, isX x = true → vidx x = a ∨ vidx x = b := by
    intro x hx hxX
    by_cases h1 : vidx x = a
    · exact Or.inl h1
    · by_cases h2 : vidx x = b
      · exact Or.inr h2
      · exact hex ⟨x, hx, hxX, h1, h2⟩
  have hsub : Finset.filter (fun w : V n => isX w) s ⊆
      insert (Sum.inl a) ({Sum.inl b} : Finset (V n)) := by
    intro x hx
    obtain ⟨hxs, hxX⟩ := Finset.mem_filter.1 hx
    obtain ⟨k, rfl⟩ := isX_to_inl hxX
    rcases hex' (Sum.inl k) hxs hxX with h | h
    · rw [vidx_inl] at h; rw [h]
      exact Finset.mem_insert_self _ _
    · rw [vidx_inl] at h; rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton.2 rfl)
  have hc := Finset.card_le_card hsub
  have hci : (insert (Sum.inl a) ({Sum.inl b} : Finset (V n))).card ≤ 2 := by
    rw [Finset.insert_eq]
    have h1 := Finset.card_union_le ({Sum.inl b} : Finset (V n)) ({Sum.inl a} : Finset (V n))
    have h2 : Finset.card ({Sum.inl b} : Finset (V n)) = 1 := Finset.card_singleton _
    have h3 : Finset.card ({Sum.inl a} : Finset (V n)) = 1 := Finset.card_singleton _
    omega
  have hle : xcnt s ≤ 2 := hc.trans hci
  omega

/-- A Y-side survivor whose index avoids a given index, from at least two
Y-side survivors. -/
theorem exists_y_idx_ne {s : Finset (V n)} (h2 : 2 ≤ ycnt s) (a : Fin n) :
    ∃ y ∈ s, isX y = false ∧ vidx y ≠ a := by
  by_contra hex
  have hex' : ∀ y ∈ s, isX y = false → vidx y = a := by
    intro y hy hyY
    by_cases h1 : vidx y = a
    · exact h1
    · exact hex ⟨y, hy, hyY, h1⟩
  have hsub : Finset.filter (fun w : V n => (isX w).not) s ⊆
      ({Sum.inr a} : Finset (V n)) := by
    intro y hy
    obtain ⟨hys, hyY⟩ := Finset.mem_filter.1 hy
    have hyF : isX y = false := eq_false_of_bnot hyY
    obtain ⟨k, rfl⟩ := isY_to_inr hyF
    have hk := hex' (Sum.inr k) hys hyF
    rw [vidx_inr] at hk; rw [hk]
    exact Finset.mem_singleton.2 rfl
  have hc := Finset.card_le_card hsub
  have h1 : Finset.card ({Sum.inr a} : Finset (V n)) = 1 := Finset.card_singleton _
  have hle : ycnt s ≤ 1 := hc.trans h1
  omega

end CrownV
