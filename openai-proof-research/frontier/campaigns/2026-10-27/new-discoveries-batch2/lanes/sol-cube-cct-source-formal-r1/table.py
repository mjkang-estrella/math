from pathlib import Path
p=Path(__file__).parent/'Finite.lean';s=p.read_text();a=s.index('set_option maxRecDepth');b=s.index('theorem obstruction')
z=[2,9,10,13,19,20];t='set_option maxRecDepth 10000\nset_option maxHeartbeats 4000000\n'
for x in z:
 for y in z:
  w=2**((x^y).bit_count())
  t+=f'@[simp] theorem w{x}_{y} : weight {x} {y} = {w} := by decide +kernel\n'
t+='theorem score_unique : ∀ x ∈ Z, score x = score 13 ↔ x = 13 := by\n  intro x hx\n  simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hx\n  rcases hx with h|h|h|h|h|h <;> subst x <;> norm_num [score,Z]\n'
t+='theorem special_weight : weight 9 13 ≠ weight 2 13 := by simp\n'
s=s[:a]+t+s[b:];s='import Mathlib.Tactic.NormNum\n'+s;p.write_text(s)
