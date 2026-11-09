from pathlib import Path
from itertools import combinations
s=Path('Finite.lean').read_text(); a=s.index('/-- Finite check (a)'); b=s.index('lemma walk_card');
Path('GData.lean').write_text(s[:a]+'end IR350452\n')
for n,name in [(4,'Four'),(3,'Three')]:
 sets=',\n'.join('{'+','.join(map(str,c))+'}' for c in combinations(range(9),n))
 p='¬ Irredundant G9 D' if n==4 else '(Irredundant G9 D ↔ ∃ i : Fin 9, walk i = D)'
 th='no_irredundant_four' if n==4 else 'irredundant_three_iff'
 t=f'''import GData
namespace IR350452
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
def sets{name} : List (Finset (Fin 9)) := [
{sets}]
lemma complete{name} : (Finset.univ : Finset (Fin 9)).powersetCard {n} = sets{name}.toFinset := by decide
lemma checked{name} : sets{name}.all (fun D => decide ({p})) = true := by decide
lemma {th} : ∀ D ∈ (Finset.univ : Finset (Fin 9)).powersetCard {n}, {p} := by
  intro D hD
  rw [complete{name}, List.mem_toFinset] at hD
  exact of_decide_eq_true ((List.all_eq_true.mp checked{name}) D hD)
end IR350452
'''
 Path(name+'.lean').write_text(t)
Path('Finite.lean').write_text('import Four\nimport Three\nnamespace IR350452\n'+s[b:])
