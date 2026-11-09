import CrownVAlg

/-!
The six irredundant-prime families of the crown binomial edge ideal
(source list: P_0, P_X, P_Y, Q_i, R_i, M_ij), realized uniformly as the
source primes `Pc T` of `CrownVAlg` for the corresponding cut sets `T`.

r4 repair of the r3 CrownVCut: `Submodule.sub_mem` takes the submodule first;
`Finset.notMem_empty`/`notMem_erase` have explicit arguments; `mixKeep` needs a
`Finset` tail; `famCut` erases from `(Xside n)`, not `n`; family arguments are
matched with `case` binders and each goal is rewritten to the concrete cut via
`rfl`-lemmas before discharging. The final mix cases are fully proved; no
`sorry` remains.
-/

namespace CrownV

section Sides
variable {n : ℕ}

/-- The X-side vertices `a_1, .., a_n`. -/
abbrev Xside (n : ℕ) : Finset (V n) := (Finset.univ : Finset (Fin n)).image Sum.inl

/-- The Y-side vertices `b_1, .., b_n`. -/
abbrev Yside (n : ℕ) : Finset (V n) := (Finset.univ : Finset (Fin n)).image Sum.inr

theorem mem_Xside {x : V n} : x ∈ Xside n ↔ isX x = true := by
  constructor
  · intro h
    obtain ⟨i, _, he⟩ := Finset.mem_image.1 h
    rw [← he]
    exact isX_inl
  · intro h
    obtain ⟨k, rfl⟩ := inl_of_isX h
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩

theorem mem_Yside {x : V n} : x ∈ Yside n ↔ isX x = false := by
  constructor
  · intro h
    obtain ⟨i, _, he⟩ := Finset.mem_image.1 h
    rw [← he]
    exact isX_inr
  · intro h
    obtain ⟨k, rfl⟩ := inr_of_isY h
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩

theorem notMem_Xside_of_isY {x : V n} (h : isX x = false) : x ∉ Xside n := by
  intro hm
  rw [mem_Xside, h] at hm
  exact absurd hm (by decide)

theorem notMem_Yside_of_isX {x : V n} (h : isX x = true) : x ∉ Yside n := by
  intro hm
  rw [mem_Yside, h] at hm
  exact absurd hm (by decide)

theorem inl_mem_Xside (i : Fin n) : Sum.inl i ∈ Xside n := mem_Xside.2 isX_inl

theorem inr_mem_Yside (i : Fin n) : Sum.inr i ∈ Yside n := mem_Yside.2 isX_inr

theorem inr_notMem_Xside (j : Fin n) : Sum.inr j ∉ Xside n := notMem_Xside_of_isY isX_inr

theorem inl_notMem_Yside (i : Fin n) : Sum.inl i ∉ Yside n := notMem_Yside_of_isX isX_inl

theorem inl_ne_inr {i j : Fin n} : (Sum.inl i : V n) ≠ Sum.inr j := by
  intro h
  cases h

/-- Members of `t` are outside `univ \ t`. -/
theorem notMem_sdiff_univ_of_mem {t : Finset (V n)} {x : V n} (hx : x ∈ t) :
    x ∉ Finset.univ \ t := by
  intro h
  exact (Finset.mem_sdiff.1 h).2 hx

/-- Nonmembers of `t` are in `univ \ t`. -/
theorem mem_sdiff_univ_of_notMem {t : Finset (V n)} {x : V n} (h : x ∉ t) :
    x ∈ Finset.univ \ t :=
  Finset.mem_sdiff.2 ⟨Finset.mem_univ x, h⟩

end Sides

section Fam
variable {n : ℕ} {K : Type*} [CommRing K]

/-- The six irredundant-prime families of the crown binomial edge ideal
(`P_0`, `P_X`, `P_Y`, `Q_i`, `R_i`, `M_ij`), indexed by their cut data. -/
inductive Fam (n : ℕ) : Type
  | zero : Fam n
  | fullX : Fam n
  | fullY : Fam n
  | delX (i : Fin n) : Fam n
  | delY (i : Fin n) : Fam n
  | mix (i j : Fin n) : Fam n

/-- The four vertices kept by the mixed family `mix i j`. -/
def mixKeep (i j : Fin n) : Finset (V n) :=
  insert (Sum.inl i) (insert (Sum.inl j) (insert (Sum.inr i) (insert (Sum.inr j) (∅ : Finset (V n)))))

/-- Cut set of each family: exactly the coordinates killed by the prime. -/
def famCut (n : ℕ) : Fam n → Finset (V n)
  | .zero => ∅
  | .fullX => Xside n
  | .fullY => Yside n
  | .delX i => (Xside n).erase (Sum.inl i)
  | .delY i => (Yside n).erase (Sum.inr i)
  | .mix i j => Finset.univ \ mixKeep i j

theorem famCut_zero (n : ℕ) : famCut n Fam.zero = (∅ : Finset (V n)) := rfl

theorem famCut_fullX (n : ℕ) : famCut n Fam.fullX = Xside n := rfl

theorem famCut_fullY (n : ℕ) : famCut n Fam.fullY = Yside n := rfl

theorem famCut_delX (n : ℕ) (i : Fin n) :
    famCut n (Fam.delX i) = (Xside n).erase (Sum.inl i) := rfl

theorem famCut_delY (n : ℕ) (i : Fin n) :
    famCut n (Fam.delY i) = (Yside n).erase (Sum.inr i) := rfl

theorem famCut_mix (n : ℕ) (i j : Fin n) :
    famCut n (Fam.mix i j) = Finset.univ \ mixKeep i j := rfl

/-- The source prime indexed by the family: `P_τ = Pc (cut τ)`. -/
noncomputable abbrev FamPrime (n : ℕ) (K : Type*) [CommRing K] (f : Fam n) :
    Ideal (PolyRing n K) :=
  Pc (K := K) (famCut n f)

theorem famPrime_zero : FamPrime (n := n) (K := K) Fam.zero =
    Pc (K := K) (∅ : Finset (V n)) := rfl

theorem famPrime_fullX : FamPrime (n := n) (K := K) Fam.fullX =
    Pc (K := K) (Xside n) := rfl

theorem famPrime_fullY : FamPrime (n := n) (K := K) Fam.fullY =
    Pc (K := K) (Yside n) := rfl

theorem famPrime_delX (i : Fin n) : FamPrime (n := n) (K := K) (Fam.delX i) =
    Pc (K := K) ((Xside n).erase (Sum.inl i)) := rfl

theorem famPrime_delY (i : Fin n) : FamPrime (n := n) (K := K) (Fam.delY i) =
    Pc (K := K) ((Yside n).erase (Sum.inr i)) := rfl

theorem famPrime_mix (i j : Fin n) : FamPrime (n := n) (K := K) (Fam.mix i j) =
    Pc (K := K) (Finset.univ \ mixKeep i j) := rfl

/-- Killed left endpoint: a minor whose X endpoint is killed lies in `Pc T`. -/
theorem minor_mem_Pc_left {T : Finset (V n)} {u v : V n} (hu : u ∈ T) :
    (minor (n := n) (K := K) u v : PolyRing n K) ∈ Pc T := by
  have e : (minor (n := n) (K := K) u v : PolyRing n K) = xx u * yy v - xx v * yy u := rfl
  rw [e]
  exact Submodule.sub_mem (Pc T)
    (Ideal.mul_mem_right (yy v) (Pc T) (xx_mem_Pc T hu))
    (Ideal.mul_mem_left (Pc T) (xx v) (yy_mem_Pc T hu))

/-- Killed right endpoint: a minor whose Y endpoint is killed lies in `Pc T`. -/
theorem minor_mem_Pc_right {T : Finset (V n)} {u v : V n} (hv : v ∈ T) :
    (minor (n := n) (K := K) u v : PolyRing n K) ∈ Pc T := by
  have e : (minor (n := n) (K := K) u v : PolyRing n K) = xx u * yy v - xx v * yy u := rfl
  rw [e]
  exact Submodule.sub_mem (Pc T)
    (Ideal.mul_mem_left (Pc T) (xx u) (yy_mem_Pc T hv))
    (Ideal.mul_mem_right (yy u) (Pc T) (xx_mem_Pc T hv))

theorem inl_notMem_mixKeep {k l i : Fin n} (hik : i ≠ k) (hil : i ≠ l) :
    Sum.inl i ∉ mixKeep k l := by
  intro h
  rcases Finset.mem_insert.1 h with h' | h'
  · exact hik (Sum.inl.inj h')
  · rcases Finset.mem_insert.1 h' with h' | h'
    · exact hil (Sum.inl.inj h')
    · rcases Finset.mem_insert.1 h' with h' | h'
      · exact inl_ne_inr h'
      · rcases Finset.mem_insert.1 h' with h' | h'
        · exact inl_ne_inr h'
        · exact Finset.notMem_empty _ h'

theorem inr_notMem_mixKeep {k l j : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) :
    Sum.inr j ∉ mixKeep k l := by
  intro h
  rcases Finset.mem_insert.1 h with h' | h'
  · exact inl_ne_inr h'.symm
  · rcases Finset.mem_insert.1 h' with h' | h'
    · exact inl_ne_inr h'.symm
    · rcases Finset.mem_insert.1 h' with h' | h'
      · exact hjk (Sum.inr.inj h')
      · rcases Finset.mem_insert.1 h' with h' | h'
        · exact hjl (Sum.inr.inj h')
        · exact Finset.notMem_empty _ h'

/-- The crown edge `a_i b_j` (`i ≠ j`) as a graph adjacency. -/
theorem cadj_inl_inr' {i j : Fin n} (hne : i ≠ j) : cadj (Sum.inl i) (Sum.inr j) :=
  cadj_inl_inr.2 hne

/-- Every crown edge minor lies in every family prime: `J ⊆ P_τ`. -/
theorem minor_mem_FamPrime (f : Fam n) {i j : Fin n} (hne : i ≠ j) :
    (minor (n := n) (K := K) (Sum.inl i) (Sum.inr j) : PolyRing n K) ∈ FamPrime n K f := by
  cases f
  case zero =>
    rw [famPrime_zero]
    have hu : (Sum.inl i : V n) ∉ (∅ : Finset (V n)) := Finset.notMem_empty _
    have hv : (Sum.inr j : V n) ∉ (∅ : Finset (V n)) := Finset.notMem_empty _
    exact minor_mem_Pc hu hv (SameC.single
      ⟨mem_sdiff_univ_of_notMem hu, mem_sdiff_univ_of_notMem hv, cadj_inl_inr' hne⟩)
  case fullX =>
    rw [famPrime_fullX]
    exact minor_mem_Pc_left (inl_mem_Xside i)
  case fullY =>
    rw [famPrime_fullY]
    exact minor_mem_Pc_right (inr_mem_Yside j)
  case delX k =>
    rw [famPrime_delX]
    by_cases hik : i = k
    · have hu : (Sum.inl i : V n) ∉ (Xside n).erase (Sum.inl k) := by
        rw [hik]
        exact Finset.notMem_erase (Sum.inl k) (Xside n)
      have hv : (Sum.inr j : V n) ∉ (Xside n).erase (Sum.inl k) :=
        fun h => inr_notMem_Xside j (Finset.mem_erase.1 h).2
      exact minor_mem_Pc hu hv (SameC.single
        ⟨mem_sdiff_univ_of_notMem hu, mem_sdiff_univ_of_notMem hv, cadj_inl_inr' hne⟩)
    · exact minor_mem_Pc_left
        (Finset.mem_erase.2 ⟨fun h => hik (Sum.inl.inj h), inl_mem_Xside i⟩)
  case delY k =>
    rw [famPrime_delY]
    by_cases hjk : j = k
    · rw [hjk]
      have hne' : i ≠ k := fun h => hne (h.trans hjk.symm)
      have hu : (Sum.inl i : V n) ∉ (Yside n).erase (Sum.inr k) :=
        fun h => inl_notMem_Yside i (Finset.mem_erase.1 h).2
      have hv : (Sum.inr k : V n) ∉ (Yside n).erase (Sum.inr k) :=
        Finset.notMem_erase (Sum.inr k) (Yside n)
      exact minor_mem_Pc hu hv (SameC.single
        ⟨mem_sdiff_univ_of_notMem hu, mem_sdiff_univ_of_notMem hv, cadj_inl_inr' hne'⟩)
    · have hv : (Sum.inr j : V n) ∈ (Yside n).erase (Sum.inr k) :=
        Finset.mem_erase.2 ⟨fun h => hjk (Sum.inr.inj h), inr_mem_Yside j⟩
      exact minor_mem_Pc_right hv
  case mix k l =>
    rw [famPrime_mix]
    by_cases hjl : j = k ∨ j = l
    · by_cases hil : i = k ∨ i = l
      · -- both endpoints survive: adjacent inside the kept four
        have hx : (Sum.inl i : V n) ∈ mixKeep k l := by
          rcases hil with h | h
          · have e : (Sum.inl i : V n) = Sum.inl k := by rw [h]
            exact Finset.mem_insert.2 (Or.inl e)
          · have e : (Sum.inl i : V n) = Sum.inl l := by rw [h]
            exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inl e)))
        have hy : (Sum.inr j : V n) ∈ mixKeep k l := by
          rcases hjl with h | h
          · have e : (Sum.inr j : V n) = Sum.inr k := by rw [h]
            exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inr
              (Finset.mem_insert.2 (Or.inl e)))))
          · have e : (Sum.inr j : V n) = Sum.inr l := by rw [h]
            exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inr
              (Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inl e)))))))
        exact minor_mem_Pc (notMem_sdiff_univ_of_mem hx) (notMem_sdiff_univ_of_mem hy)
          (SameC.single ⟨mem_sdiff_univ_of_notMem (notMem_sdiff_univ_of_mem hx),
            mem_sdiff_univ_of_notMem (notMem_sdiff_univ_of_mem hy), cadj_inl_inr' hne⟩)
      · -- a_i killed
        have hik : i ≠ k := fun h => hil (Or.inl h)
        have hil' : i ≠ l := fun h => hil (Or.inr h)
        exact minor_mem_Pc_left
          (mem_sdiff_univ_of_notMem (inl_notMem_mixKeep hik hil'))
    · -- b_j killed
      have hjk : j ≠ k := fun h => hjl (Or.inl h)
      have hjl' : j ≠ l := fun h => hjl (Or.inr h)
      exact minor_mem_Pc_right
        (mem_sdiff_univ_of_notMem (inr_notMem_mixKeep hjk hjl'))

end Fam

end CrownV
