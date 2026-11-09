from pathlib import Path
from fractions import Fraction as F
from math import lcm
import json
L=Path(__file__).resolve().parent
C=json.loads((L/'coverage.json').read_text())
raw=json.loads((L/'frozen/rational-realizations.json').read_text())
for tag in ['G','H']:
 t=[f'import Instance{tag}',f'import Data{tag}','import RealCore','set_option maxRecDepth 10000','set_option maxHeartbeats 800000','noncomputable section','namespace TripleCertificates','open FullereneGeometry',f'theorem Dpos{tag} : (0:ℝ) < D{tag} := by norm_num [D{tag}]',f'theorem qbind{tag} (i : Fin 32) : rv (A{tag} i) = (D{tag}:ℝ) • q{tag} i := by',f' fin_cases i <;> ext k <;> fin_cases k <;> norm_num [rv, A{tag}, D{tag}, q{tag}]',f'theorem pbind{tag} (v : Fin 60) : rp (P{tag} v) = p{tag} v := by',f' fin_cases v <;> ext k <;> fin_cases k <;> norm_num [rp, rv, P{tag}, p{tag}]','end TripleCertificates']
 old=L/f'Bindings{tag}.lean'
 if old.exists() and not (L/'failures'/f'Bindings{tag}-unsplit.lean.txt').exists():
  d=L/'failures';d.mkdir(exist_ok=True);(d/f'Bindings{tag}-unsplit.lean.txt').write_bytes(old.read_bytes())
 modules=[]
 for kind,count in [('Q',32),('P',60)]:
  for start in range(0,count,4):
   name=f'Bind{tag}{kind}{start//4:02d}';modules.append(name)
   rows=t[:8]
   for n in range(start,start+4):
    if kind=='Q':
     q=[F(x) for x in raw[tag]['dual_vertices'][n]];D=C[tag]['D']
     rows += [f'theorem qb{tag}{n:02d} : rv (A{tag} {n}) = (D{tag}:ℝ) • q{tag} {n} := by',' ext k; fin_cases k']
     for x in q:rows += [f' · change (↑({int(x*D)} : ℤ) : ℝ) = (↑({D} : ℤ) : ℝ) * (({x.numerator}:ℝ) / {x.denominator})','   norm_num']
    else:
     p=[F(x) for x in raw[tag]['primal_vertices'][n]];den=lcm(*(x.denominator for x in p))
     rows += [f'theorem pb{tag}{n:02d} : rp (P{tag} {n}) = p{tag} {n} := by',' ext k; fin_cases k']
     for x in p:rows += [f' · change ((↑({int(x*den)} : ℤ) : ℝ) / (↑({den} : ℤ) : ℝ)) = (({x.numerator} : ℝ) / {x.denominator})','   norm_num']
   (L/f'{name}.lean').write_text('\n'.join(rows+['end TripleCertificates'])+'\n')
 out=['import '+m for m in modules]+['namespace TripleCertificates','open FullereneGeometry',t[9],t[10],' fin_cases i']
 out += [f' · exact qb{tag}{n:02d}' for n in range(32)]
 out += [t[12],' fin_cases v']
 out += [f' · exact pb{tag}{n:02d}' for n in range(60)]+['end TripleCertificates']
 # use explicit declarations, independent of the old unsplit line offsets
 out=['import '+m for m in modules]+['namespace TripleCertificates','open FullereneGeometry',f'theorem Dpos{tag} : (0:ℝ) < D{tag} := by norm_num [D{tag}]',f'theorem qbind{tag} (i : Fin 32) : rv (A{tag} i) = (D{tag}:ℝ) • q{tag} i := by',' fin_cases i']+[f' · exact qb{tag}{n:02d}' for n in range(32)]+[f'theorem pbind{tag} (v : Fin 60) : rp (P{tag} v) = p{tag} v := by',' fin_cases v']+[f' · exact pb{tag}{n:02d}' for n in range(60)]+['end TripleCertificates']
 old.write_text('\n'.join(out)+'\n')
 t=[f'import Data{tag}','set_option maxRecDepth 10000','namespace TripleCertificates']
 for j,ids in enumerate(raw[tag]['dual_facets']):
  # primal vertices are indexed by the triangular dual faces
  i,k,h=ids
  t.append(f'theorem listed{tag}{j:02d} : 0 < (P{tag} {j}).den ∧ core (A{tag} {i}) (A{tag} {k}) (A{tag} {h}) D{tag} (P{tag} {j}) ∧ (∀ t, dp (A{tag} t) (P{tag} {j}).num ≤ D{tag} * (P{tag} {j}).den) := by decide +kernel')
 t.append('end TripleCertificates');(L/f'Listed{tag}.lean').write_text('\n'.join(t)+'\n')
print('bindings and listed certificates generated')
