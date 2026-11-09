from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
M=L.parents[3]/'2026-10-14/formal/.lake/packages/mathlib/Mathlib'
# Explicit local path, no Lean or build invocation.
M=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/Mathlib')
paths=sorted((M/'Computability').glob('*.lean'))
rows=[];matches=[]
for p in paths:
 if p.stem not in ['DFA','NFA','Language','RegularExpressions','PumpingLemma','MyhillNerode']:continue
 q=L/'frozen-library'/p.name;q.parent.mkdir(exist_ok=True)
 d=hashlib.sha256(p.read_bytes()).hexdigest();shutil.copyfile(p,q)
 assert d==hashlib.sha256(p.read_bytes()).hexdigest()==hashlib.sha256(q.read_bytes()).hexdigest()
 rows.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':d})
 for i,line in enumerate(q.read_text().splitlines(),1):
  if any(x in line.lower() for x in ['pumping','isregular','reverse','reversal','map','complement','eval']):
   if line.startswith(('theorem','def ','lemma','protected theorem','noncomputable def')):matches.append([p.name,i,line[:200]])
(L/'library-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
(L/'library-assessment.json').write_text(json.dumps({'inventory':[p.name for p in paths],'selected_declarations':matches,'scope':'Computability top-level only; no claim of global absence; no Lean run'},indent=2)+'\n')
print(json.dumps({'files':len(rows),'matches':matches[:60]},indent=2))
