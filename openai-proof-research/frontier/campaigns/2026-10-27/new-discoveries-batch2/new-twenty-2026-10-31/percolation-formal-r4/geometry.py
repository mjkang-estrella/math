from pathlib import Path
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');S=R/'packet/src'
mods=[]
for i in range(31):
 m=f'Geometry{i:02d}';mods.append(m)
 (S/(m+'.lean')).write_text(f'''import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem line_fixed5_{i} : ∀ p : Points 5,
    step PG5 5 (fun x => incidence x {i}) p = incidence p {i} := by decide
theorem join_unique5_{i} : ∀ q l k : Points 5,
    ({i} : Points 5) ≠ q → incidence {i} l = true → incidence q l = true →
    incidence {i} k = true → incidence q k = true → l = k := by decide
end Percolation
''')
def combine(name,statement,args):
 out=[f'theorem {name} : {statement} := by', '  intro p', '  have h : '+ ' ∨ '.join(f'p.val = {i}' for i in range(31))+' := by omega', '  rcases h with '+' | '.join(f'h{i}' for i in range(31))]
 for i in range(31):out += [f'  · have he : p = {i} := Fin.ext h{i}',f'    subst p',f'    exact {name}_{i}'+args]
 return '\n'.join(out)+'\n'
orig=(S/'Noncollinear.lean').read_text();start=orig.index('theorem line_fixed5');end=orig.index('theorem line_nonfull5')
orig=orig[:start]+combine('line_fixed5','∀ l p : Points 5, step PG5 5 (fun x => incidence x l) p = incidence p l','')+'\n'+combine('join_unique5','∀ p q l k : Points 5, p ≠ q → incidence p l = true → incidence q l = true → incidence p k = true → incidence q k = true → l = k','')+orig[end:]
start=orig.index('theorem off_join_noncollinear5');end=orig.index('theorem percolates_noncollinear5')
orig=orig[:start]+'''theorem off_join_noncollinear5 (p q l r : Points 5)
    (hne : p ≠ q) (hp : incidence p l = true) (hq : incidence q l = true)
    (hr : incidence r l = false) : Noncollinear5 p q r := by
  intro k ⟨hpk,hqk,hrk⟩
  have he := join_unique5 p q l k hne hp hq hpk hqk
  subst k
  rw [hr] at hrk
  contradiction

'''+orig[end:]
start=orig.index('theorem noncollinear_ne5');orig=orig[:start]+'''theorem noncollinear_ne5 (p q r : Points 5) (h : Noncollinear5 p q r) : p ≠ q := by
  intro he
  subst q
  obtain ⟨l,hp,hr⟩ := pair_on_line5 p r
  exact h l ⟨hp,hp,hr⟩

theorem noncollinear_fixed5 (p : Points 5) (h : Noncollinear5 0 25 p) :
    incidence p 30 = false := by
  cases hi : incidence p 30
  · rfl
  · exact False.elim (h 30 ⟨by decide,by decide,hi⟩)
end Percolation
'''
orig='\n'.join('import '+m for m in mods)+'\n'+orig
(S/'Noncollinear.lean').write_text(orig)
(R/'geometry-order.txt').write_text('\n'.join(mods+['Noncollinear'])+'\n')
