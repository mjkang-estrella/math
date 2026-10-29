import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY))
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
import json,hashlib,re,zipfile,datetime
from pathlib import Path
R=Path(__file__).resolve().parent
mods=['Source','Boundary','Gadget','Edges','Degrees']
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
log=(R/'logs/OriginAudit.log').read_text()
rows=re.findall(r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$',log,re.M|re.S)
assert len(rows)==int(re.search(r'AUDIT_TOTAL (\d+)',log)[1]);assert len({r[1] for r in rows})==len(rows)
(R/'formal/AuditPrint.lean').write_text('import Degrees\nset_option autoImplicit false\nset_option warningAsError true\nset_option pp.privateNames true\n#print EdgeIrregulator.SourceClaim\n#print EdgeIrregulator.MinimumSourceClaim\n'+''.join('#check '+r[1]+'\n#print axioms '+r[1]+'\n' for r in sorted(rows)))
pins=json.loads((R/'pins.json').read_text());deps=[]
for n in (R/'formal/dependencies.txt').read_text().splitlines():
 if n in mods:continue
 for p in pins['packages']:
  f=Path(p['path'])/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.olean')
  if f.exists():deps.append({'path':str(f),'sha256':sha(f)});break
(R/'dependency-hashes.json').write_text(json.dumps(deps,indent=2)+'\n')
print('Inventory',len(rows),'dependencies',len(deps))
