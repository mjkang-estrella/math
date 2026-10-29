from pathlib import Path
p=Path(__file__).parent/'component/formal/Lower.lean';s=p.read_text();a=s.index(' theorem block_cost');b=s.index(' theorem deleted_card_sum');s=s[:a]+''' theorem cost_bits : ∀ r : Fin 8 → Bool,
    (Finset.univ.filter (fun k => r k = false)).card = diamondCost r + pathCost r := by
  decide +kernel
 theorem block_cost {t : ℕ} (S : Finset (Sym2 (Vertex t))) (i : Fin t) :
    (blockDeleted S i).card = diamondCost (mask S i) + pathCost (mask S i) := by
  rw [← cost_bits]
  congr 1
  ext k
  by_cases hk : edge (i,k) ∈ S <;> simp [blockDeleted,mask,hk]
'''+s[b:];p.write_text(s)
