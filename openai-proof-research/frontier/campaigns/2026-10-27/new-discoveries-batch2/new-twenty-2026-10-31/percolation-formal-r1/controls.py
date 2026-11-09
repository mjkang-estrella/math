from pathlib import Path
import json
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r1')
d=json.loads((root.parent/'expanded-corpus-r164/outputs/percolation.json').read_text())[1]['witness']
e=json.loads((root.parent/'expanded-corpus-r164/outputs/percolation-three-round.json').read_text())
(root/'src/ControlBase.lean').write_text('''import Plane5
namespace Percolation
def maskSet (m : Nat) : Infection 5 := fun p => m.testBit p.val
end Percolation
''')
for r,t,w,closures in [(4,2,d['mask'],d['deletion_closures']),(5,3,e['mask'],e['deletion_closures'])]:
 s=f'''import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
def witness{r} : Infection 5 := maskSet {w}
def separators{r} : List Nat := {str([closures.get(str(i),0) for i in range(31)])}
def separator{r} (v : Points 5) : Infection 5 := maskSet (separators{r}[v.val]!)
theorem full{r} : Full (rounds PG5 {r} witness{r} {t}) := by decide
theorem early{r} : ∀ k : Fin {t}, ¬ Full (rounds PG5 {r} witness{r} k.val) := by decide
theorem time{r} : TimeIs PG5 {r} witness{r} {t} :=
  ⟨full{r}, fun k hk => early{r} ⟨k,hk⟩⟩
'''
 # split deletion certificates, each checking one fixed point to avoid expression blowup
 for i in range(31):
  if str(i) not in closures: continue
  mod=f'Sep{r}_{i}'
  (root/f'src/{mod}.lean').write_text(f'''import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep{r}_{i} :
    (∀ p : Points 5, p ≠ {i} → maskSet {w} p = true → maskSet {closures[str(i)]} p = true) ∧
    (∀ p, step PG5 {r} (maskSet {closures[str(i)]}) p = maskSet {closures[str(i)]} p) ∧
    maskSet {closures[str(i)]} {i} = false := by decide
end Percolation
''')
 s=s.replace('import ControlBase','import ControlBase\n'+'\n'.join(f'import Sep{r}_{i}' for i in range(31) if str(i) in closures))
 s+=f'''theorem minimal{r} : Minimal PG5 {r} witness{r} := by
  apply minimal_from_separators PG5 {r} witness{r} ⟨{t}, full{r}⟩
  intro v hv
  refine ⟨separator{r} v, ?_⟩
  have casesV : '''+' ∨ '.join(f'v = {i}' for i in range(31) if str(i) in closures)+f''' := by
    revert hv
    revert v
    decide
  rcases casesV with '''+' | '.join('h'+str(i) for i in range(31) if str(i) in closures)+'\n'
 for i in range(31):
  if str(i) not in closures: continue
  s+=f'''  · subst v
    exact ⟨sep{r}_{i}.1, funext sep{r}_{i}.2.1, sep{r}_{i}.2.2⟩
'''
 s+=f'theorem control{r} : ∃ a, Minimal PG5 {r} a ∧ TimeIs PG5 {r} a {t} := ⟨witness{r}, minimal{r}, time{r}⟩\nend Percolation\n'
 (root/f'src/Control{r}.lean').write_text(s)
mods=['Definitions','Plane5','ControlBase']+[f'Sep{r}_{i}' for r,closures in [(4,d['deletion_closures']),(5,e['deletion_closures'])] for i in range(31) if str(i) in closures]+['Control4','Control5']
(root/'module-order.txt').write_text('\n'.join(mods)+'\n')
