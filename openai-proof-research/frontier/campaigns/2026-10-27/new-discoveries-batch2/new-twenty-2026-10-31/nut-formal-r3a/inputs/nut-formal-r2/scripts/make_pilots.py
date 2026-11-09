from pathlib import Path
import json
r=Path(__file__).resolve().parents[1]
a=json.loads((r/'inputs/expanded-corpus-r111/outputs/nut-exact-certificates.json').read_text())
def nodes(a):
 if not a:return 1
 return 1+sum(nodes([[x for k,x in enumerate(row) if k!=j] for row in a[1:]]) for j,v in enumerate(a[0]) if v)
def computation(x):
 a=x['matrix']
 if 'zero_principal_minor' in x:
  i=x['zero_principal_minor'];a=[[v for j,v in enumerate(row) if j!=i] for k,row in enumerate(a) if k!=i]
 return a
chosen=[('HardDet',max((x for x in a if 'det' in x),key=lambda x:nodes(computation(x)))),('HardCofactor',max((x for x in a if 'zero_principal_minor' in x),key=lambda x:nodes(computation(x))))]
meta=[]
for name,x in chosen:
 a=x['matrix'];s='import VerifiedDet\nnamespace Nut8.'+name+'\n'
 s+='def C : Matrix (Fin 8) (Fin 8) ℤ := !!['+'; '.join(', '.join(map(str,row)) for row in a)+']\n'
 if 'det' in x:s+=f'theorem certificate : C.det = {x["det"]} := by\n  rw [← sparseDet_eq_det]\n  decide +kernel\n'
 else:
  i=x['zero_principal_minor'];s+=f'theorem certificate : C.adjugate {i} {i} = 0 := by\n  rw [← sparseDet_principal]\n  decide +kernel\n'
 s+='end Nut8.'+name+'\n';(r/'formal'/(name+'.lean')).write_text(s)
 meta.append(dict(module=name,recursive_nodes=nodes(computation(x)),certificate=x))
(r/'pilot-selection.json').write_text(json.dumps(meta,indent=2)+'\n');print([(x['module'],x['recursive_nodes']) for x in meta])
