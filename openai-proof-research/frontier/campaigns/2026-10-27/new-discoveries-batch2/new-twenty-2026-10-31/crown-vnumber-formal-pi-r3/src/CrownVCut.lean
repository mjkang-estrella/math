import CrownVAlg

/-!
The six irredundant-prime families of the crown binomial edge ideal
(source list: P_0, P_X, P_Y, Q_i, R_i, M_ij), realized uniformly as the
source primes `Pc T` of `CrownVAlg` for the corresponding cut sets `T`.
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
  cases hm

theorem notMem_Yside_of_isX {x : V n} (h : isX x = true) : x ∉ Yside n := by
  intro hm
  rw [mem_Yside, h] at hm
  cases hm

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
  exact h.2 hx

/-- Nonmembers of `t` are in `univ \ t`. -/
theorem mem_sdiff_univ_of_notMem {t : Finset (V n)} {x : V n} (h : x ∉ t) :
    x ∈ Finset.univ \ t :=
  ⟨Finset.mem_univ, h⟩

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
  insert (Sum.inl i) (insert (Sum.inl j) (insert (Sum.inr i) (Sum.inr j)))

/-- Cut set of each family: exactly the coordinates killed by the prime. -/
def famCut (n : ℕ) : Fam n → Finset (V n)
  | .zero => ∅
  | .fullX => Xside n
  | .fullY => Yside n
  | .delX i => Xside n.erase (Sum.inl i)
  | .delY i => Yside n.erase (Sum.inr i)
  | .mix i j => Finset.univ \ mixKeep n i j

/-- The source prime indexed by the family: `P_τ = Pc (cut τ)`. -/
noncomputable abbrev FamPrime (n : ℕ) (K : Type*) [CommRing K] (f : Fam n) :
    Ideal (PolyRing n K) :=
  Pc (K := K) (famCut n f)

/-- Killed left endpoint: a minor whose X endpoint is killed lies in `Pc T`. -/
theorem minor_mem_Pc_left {T : Finset (V n)} {u v : V n} (hu : u ∈ T) :
    (minor (n := n) (K := K) u v : PolyRing n K) ∈ Pc T := by
  have e : (minor (n := n) (K := K) u v : PolyRing n K) = xx u * yy v - xx v * yy u := rfl
  rw [e]
  exact Submodule.sub_mem (Ideal.mul_mem_right (yy v) (Pc T) (xx_mem_Pc T hu))
    (Ideal.mul_mem_left (Pc T) (xx v) (yy_mem_Pc T hu))

/-- Killed right endpoint: a minor whose Y endpoint is killed lies in `Pc T`. -/
theorem minor_mem_Pc_right {T : Finset (V n)} {u v : V n} (hv : v ∈ T) :
    (minor (n := n) (K := K) u v : PolyRing n K) ∈ Pc T := by
  have e : (minor (n := n) (K := K) u v : PolyRing n K) = xx u * yy v - xx v * yy u := rfl
  rw [e]
  exact Submodule.sub_mem (Ideal.mul_mem_left (Pc T) (xx u) (yy_mem_Pc T hv))
    (Ideal.mul_mem_right (yy u) (Pc T) (xx_mem_Pc T hv))

theorem inl_notMem_mixKeep {k l i : Fin n} (hik : i ≠ k) (hil : i ≠ l) :
    Sum.inl i ∉ mixKeep n k l := by
  intro h
  rcases Finset.mem_insert.1 h with h' | h'
  · exact hik (Sum.inl.inj h')
  · rcases Finset.mem_insert.1 h' with h'' | h''
    · exact hil (Sum.inl.inj h'')
    · rcases Finset.mem_insert.1 h'' with h3 | h3
      · exact inl_ne_inr h3
      · exact inl_ne_inr h3

theorem inr_notMem_mixKeep {k l j : Fin n} (hjk : j ≠ k) (hjl : j ≠ l) :
    Sum.inr j ∉ mixKeep n k l := by
  intro h
  rcases Finset.mem_insert.1 h with h' | h'
  · exact hjk (Sum.inr.inj h')
  · rcases Finset.mem_insert.1 h' with h'' | h''
    · exact hjl (Sum.inr.inj h'')
    · rcases Finset.mem_insert.1 h'' with h3 | h3
      · exact inl_ne_inr h3.symm
      · exact inl_ne_inr h3.symm

/-- The crown edge `a_i b_j` (`i ≠ j`) as a graph adjacency. -/
theorem cadj_inl_inr' {i j : Fin n} (hne : i ≠ j) : cadj (Sum.inl i) (Sum.inr j) :=
  cadj_inl_inr.2 hne

/-- Every crown edge minor lies in every family prime: `J ⊆ P_τ`. -/
theorem minor_mem_FamPrime (f : Fam n) {i j : Fin n} (hne : i ≠ j) :
    (minor (n := n) (K := K) (Sum.inl i) (Sum.inr j) : PolyRing n K) ∈ FamPrime n K f := by
  cases f
  · -- zero: both endpoints survive and are adjacent in the full graph
    refine minor_mem_Pc Finset.notMem_empty Finset.notMem_empty ?_
    have hu : (Finset.univ : Finset (V n)) \ (∅ : Finset (V n)) = Finset.univ :=
      Finset.sdiff_empty
    rw [hu]
    exact SameC.single ⟨Finset.mem_univ, Finset.mem_univ, cadj_inl_inr' hne⟩
  · -- fullX: a_i is killed
    exact minor_mem_Pc_left inl_mem_Xside
  · -- fullY: b_j is killed
    exact minor_mem_Pc_right inr_mem_Yside
  · -- delX k
    by_cases hik : i = k
    · subst hik
      refine minor_mem_Pc (Finset.notMem_erase.2 (Or.inl rfl))
        (Finset.notMem_erase.2 (Or.inr inr_notMem_Xside)) ?_
      exact SameC.single ⟨Finset.mem_univ, Finset.notMem_erase.2 (Or.inl rfl),
        Finset.notMem_erase.2 (Or.inr inr_notMem_Xside), cadj_inl_inr' hne⟩
    · exact minor_mem_Pc_left
        (Finset.mem_erase.2 ⟨inl_mem_Xside, fun h => hik (Sum.inl.inj h)⟩)
  · -- delY k
    by_cases hjk : j = k
    · subst hjk
      refine minor_mem_Pc (Finset.notMem_erase.2 (Or.inr inl_notMem_Yside))
        (Finset.notMem_erase.2 (Or.inl rfl)) ?_
      exact SameC.single ⟨Finset.mem_univ, Finset.notMem_erase.2 (Or.inr inl_notMem_Yside),
        Finset.notMem_erase.2 (Or.inl rfl), cadj_inl_inr' hne⟩
    · exact minor_mem_Pc_right
        (Finset.mem_erase.2 ⟨inr_mem_Yside, fun h => hjk (Sum.inr.inj h)⟩)
  · -- mix k l: T = univ ∖ keep, survivors live in keep
    by_cases hil : i = k ∨ i = l
    · by_cases hjl : j = k ∨ j = l
      · -- both endpoints survive: adjacent inside the kept four
        have hik : ¬(i = k ∧ i = l) := by
          intro h
          exact hne (by
            rcases hil with h1 | h1
            · exact h.1
            · exact (h.2).symm ▸ h1)
        have hjk' : ¬(j = k ∧ j = l) := by
          intro h
          exact absurd (by
            rcases hjl with h1 | h1
            · exact h.1
            · exact (h.2).symm ▸ h1) (fun h => hne h.symm) 
        sorry
      · -- b_j killed
        sorry
    · -- a_i killed
      sorry

end Fam

end CrownV
