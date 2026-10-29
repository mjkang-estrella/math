from pathlib import Path
p=Path(__file__).parent/'component/formal/Lower.lean';s=p.read_text();s=s.replace('  unfold diamondCost pathCost bit mask\n  split_ifs <;> omega','  have hb : ∀ k, 1 - bit (mask S i) k = if edge (i,k) ∈ S then 1 else 0 := by\n    intro k\n    by_cases hk : edge (i,k) ∈ S <;> simp [bit,mask,hk]\n  simp only [diamondCost,pathCost,hb]\n  omega');p.write_text(s)
