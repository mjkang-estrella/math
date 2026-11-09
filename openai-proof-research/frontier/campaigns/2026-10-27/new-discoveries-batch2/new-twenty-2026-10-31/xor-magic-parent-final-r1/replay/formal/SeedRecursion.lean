import SeedIteration
import ColourSeed16Closed4
import ColourSeed16Open5
import ColourSeed32Closed4
import ColourSeed32Open5
namespace XorMagic
/-- Two base cases are essential: the lift increments the exponent by two. -/
theorem seeds_all (n : ℕ) (hn : 4 ≤ n) : SeedExists n 4 true ∧ SeedExists n 5 false := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h4 : n = 4
    · subst n
      exact ⟨⟨16,_,inferInstance,⟨Seed16Closed4.coloured⟩⟩,
        ⟨16,_,inferInstance,⟨Seed16Open5.coloured⟩⟩⟩
    by_cases h5 : n = 5
    · subst n
      exact ⟨⟨32,_,inferInstance,⟨Seed32Closed4.coloured⟩⟩,
        ⟨32,_,inferInstance,⟨Seed32Open5.coloured⟩⟩⟩
    obtain ⟨hc,ho⟩ := ih (n-2) (by omega) (by omega)
    have step {d : ℕ} {closed : Bool} (h : SeedExists (n-2) d closed) (hd : 4 ≤ d)
        (hp : if closed then Even d else Odd d) : SeedExists n d closed := by
      obtain ⟨m,G,dec,⟨S⟩⟩ := h
      have : Nonempty (Fin m) := by
        have hmag := S.seed.magic
        cases closed <;> exact hmag.1.nonempty
      have hh := S.iterate hd hp
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ n)] using hh
    exact ⟨step hc (by decide) (by decide),step ho (by decide) (by decide)⟩
end XorMagic
