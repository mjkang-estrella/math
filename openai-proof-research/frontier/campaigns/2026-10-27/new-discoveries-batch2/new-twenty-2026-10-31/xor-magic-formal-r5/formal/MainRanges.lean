import SeedIntervals
namespace XorMagic
theorem main_ranges (n : ℕ) (hn : 6 ≤ n) :
    (∀ q, Odd q → 5 ≤ q → q ≤ 2^n-9 → OpenExists n q) ∧
    (∀ q, Even q → 4 ≤ q → q ≤ 2^n-8 → ClosedExists n q) := by
  obtain ⟨hc,ho⟩ := seeds_all (n-2) (by omega)
  have he : n-2+2 = n := by omega
  have hp : 4*2^(n-2) = 2^n := by
    conv_rhs => rw [← he, pow_add]
    ring
  constructor
  · obtain ⟨m,G,dec,⟨S⟩⟩ := ho
    have hm : m = 2^(n-2) := by
      obtain ⟨_,l,_⟩ := S.seed.magic
      simpa using card_of_label l
    have : Nonempty (Fin m) := S.seed.magic.1.nonempty
    intro q hq hl hu
    have hh := S.open_interval (by decide) (by decide) q hq hl (by rw [hm]; omega)
    simpa only [he] using hh
  · obtain ⟨m,G,dec,⟨S⟩⟩ := hc
    have hm : m = 2^(n-2) := by
      obtain ⟨_,l,_⟩ := S.seed.magic
      simpa using card_of_label l
    have : Nonempty (Fin m) := S.seed.magic.1.nonempty
    intro q hq hl hu
    have hh := S.closed_interval (by decide) (by decide) q hq hl (by rw [hm]; omega)
    simpa only [he] using hh
end XorMagic
