from pathlib import Path
import json,sys,hashlib
r=Path(__file__).resolve().parents[1]
cs=json.loads((r/'inputs/nut-formal-r2/all-normalized-certificates.json').read_text())
size=int(sys.argv[1]) if len(sys.argv)>1 else 32
limit=int(sys.argv[2]) if len(sys.argv)>2 else len(cs)
mods=[]
for start in range(0,min(limit,len(cs)),size):
 name=f'Certificates{start//size:04d}';mods.append(name)
 lines=['import VerifiedDet',f'namespace Nut8.{name}']
 for k,c in enumerate(cs[start:min(start+size,limit)],start):
  a=c['matrix'];lit='!!['+'; '.join(', '.join(str(x) for x in row) for row in a)+']'
  lines.append(f'def C{k} : Matrix (Fin 8) (Fin 8) ℤ := {lit}')
  if 'det' in c:
   stmt=f'C{k}.det = ({c["det"]} : ℤ)';correct='sparseDet_eq_det'
  else:
   i=c['zero_principal_minor'];stmt=f'C{k}.adjugate {i} {i} = 0';correct='sparseDet_principal'
  lines += [f'theorem certificate{k} : {stmt} := by',f'  rw [← {correct}]','  decide +kernel']
 lines += [f'end Nut8.{name}']
 (r/'formal'/(name+'.lean')).write_text('\n'.join(lines)+'\n')
(r/'certificate-modules.json').write_text(json.dumps({'size':size,'count':min(limit,len(cs)),'modules':mods,'input_sha256':hashlib.sha256((r/'inputs/nut-formal-r2/all-normalized-certificates.json').read_bytes()).hexdigest()},indent=2)+'\n')
print('generated',min(limit,len(cs)),'certificates in',len(mods),'modules')
