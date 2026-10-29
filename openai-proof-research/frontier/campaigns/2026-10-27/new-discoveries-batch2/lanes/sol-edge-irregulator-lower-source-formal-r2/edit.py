from pathlib import Path
p=Path(__file__).parent/'component/formal/Local.lean'
s=p.read_text().replace('set_option warningAsError true','set_option warningAsError true\nset_option linter.unusedSimpArgs false')
s=s.replace('simp [ha,hb,hab]','simp [Finset.filter_insert, Finset.filter_singleton,ha,hb,hab]')
import re
for v, ns, d in [(1,'node i 0,node i 2,node i 3','db'),(2,'node i 0,node i 1,node i 4','dc'),(3,'node i 0,node i 1','dd'),(4,'node i 2,node i 5','dx'),(5,'node i 4,hub t','dy')]:
 start=s.index(' theorem degree_'+{1:'b',2:'c',3:'d',4:'x',5:'y'}[v])
 a=s[:start]; b=s[start:]
 b=re.sub(r'  simp only \[neighbors,[^\n]*\]',f'  change (({{{ns}}} : Finset (Vertex t)).filter (fun w => s(node i {v},w) ∉ S)).card = {d} (mask S i)',b,count=1)
 s=a+b
# simplify ends using dsimp rather than numeral simp
s=s.replace('  · simp only [db,bit,mask,edge,ends,Matrix.cons_val_zero,Matrix.cons_val_one,\n      Matrix.cons_val_succ,Fin.isValue,Sym2.eq_swap]','  · dsimp [db,bit,mask,edge,ends]\n    simp only [Sym2.eq_swap]')
for d in ['dc','dd','dx','dy']:
 s=s.replace(f'  · simp only [{d},bit,mask,edge,ends,Matrix.cons_val_zero,Matrix.cons_val_one,\n      Matrix.cons_val_succ,Fin.isValue,Sym2.eq_swap]',f'  · dsimp [{d},bit,mask,edge,ends]\n    simp only [Sym2.eq_swap]')
p.write_text(s)
