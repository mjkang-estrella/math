import PolynexusLiteral
example (n : ℕ) (hn : 0 < n) :
    120*(((PNZ n ×ˢ PNZ n).filter (fun p => p.1*p.2 ≠ 0)).card : ℤ) =
      (n+1:ℤ)^7-(n:ℤ)^7+(n+1:ℤ)^3+(n:ℤ)^3 := by
  exact polynexus_literal n hn
