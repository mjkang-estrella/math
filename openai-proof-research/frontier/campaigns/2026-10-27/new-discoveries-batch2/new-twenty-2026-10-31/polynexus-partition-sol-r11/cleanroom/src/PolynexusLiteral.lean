import PolynexusEval

/-- The actual source monoid, expressed using signed one-based parameters. -/
def PSourceMn (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℕ) :=
  {X | X = 0 ∨ ∃ d k m, PSrcLeg n d k m ∧ X = PSrc n d k m}

/-- The printed min/max bounds are exactly the five legality inequalities. -/
theorem PSrcLeg_printed (n : ℕ) (d : ℤ) (k m : ℕ) :
    PSrcLeg n d k m ↔
      1 - min 0 d ≤ (k:ℤ) ∧ k ≤ m ∧ (m:ℤ) ≤ (n:ℤ) - max 0 d := by
  dsimp [PSrcLeg]
  constructor <;> intro h <;> rcases h with ⟨h1,h2,h3⟩ <;>
    by_cases hd : 0 ≤ d
  · rw [min_eq_left hd, max_eq_right hd]
    omega
  · rw [min_eq_right (by omega : d ≤ 0), max_eq_left (by omega : d ≤ 0)]
    omega
  · simp only [min_eq_left hd, max_eq_right hd] at h1 h3
    omega
  · simp only [min_eq_right (by omega : d ≤ 0), max_eq_left (by omega : d ≤ 0)] at h1 h3
    omega

/-- Membership of the finite operand set is exactly membership of the
source monoid with its genuine zero removed. -/
theorem PNZ_source (n : ℕ) (X : Matrix (Fin n) (Fin n) ℕ) :
    X ∈ PNZ n ↔ X ∈ PSourceMn n ∧ X ≠ 0 := by
  constructor
  · intro hx
    obtain ⟨x,hx,he⟩ := Finset.mem_image.1 hx
    have hl := PLeg_leg hx
    have hs := PSrcLeg_of_leg hl
    have hb := PBlk_eq_PSrc hl
    refine ⟨Or.inr ⟨(x.2.1:ℤ)-x.1,x.1+1,x.1+x.2.2+1,hs,?_⟩, ?_⟩
    · exact he.symm.trans hb
    · rw [← he, show PB n x = PSrc n ((x.2.1:ℤ)-x.1) (x.1+1) (x.1+x.2.2+1) from hb]
      exact PSrc_ne_zero hs
  · rintro ⟨hx,hnz⟩
    rcases hx with hz | ⟨d,k,m,hl,he⟩
    · exact False.elim (hnz hz)
    · apply Finset.mem_image.2
      refine ⟨(srcA k,srcB d k,srcE k m), PLeg_mem.2 ?_, ?_⟩
      · have h := srcDict_leg hl
        dsimp
        omega
      · exact (PSrc_eq_PBlk hl).symm.trans he.symm

/-- Full literal integer identity; the finite set is precisely the ordered
nonzero source operands, by `PNZ_source`, and `*` is ordinary matrix product. -/
theorem polynexus_literal (n : ℕ) (_hn : 0 < n) :
    120*(((PNZ n ×ˢ PNZ n).filter (fun p => p.1*p.2 ≠ 0)).card : ℤ) =
      (n+1:ℤ)^7-(n:ℤ)^7-(n+1:ℤ)^3+(n:ℤ)^3 :=
  polynexus_integer n

/-- The same source definition at n=1 is included, with one nonzero pair. -/
theorem polynexus_one : psi 1 = 1 := by
  have h := polynexus_integer 1
  norm_num at h
  omega
