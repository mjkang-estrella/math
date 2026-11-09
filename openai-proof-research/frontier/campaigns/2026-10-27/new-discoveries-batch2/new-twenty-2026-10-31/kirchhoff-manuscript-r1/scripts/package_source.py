from pathlib import Path
import json,hashlib,zipfile
D=Path(__file__).resolve().parents[1]
J=json.loads((D/'paper/manuscript.json').read_text())
text=['# Ordinary proof of the MathDB 349441 counterexample','AI-assisted DRAFT. Zero accepted credit. No priority claim.']
for p in J[:4]:
 text+=['## '+p['title']]
 for s in p['sections']:
  text+=['### '+s[0]]+[t[3:] if t.startswith('EQ:') else t for t in s[1:] if not t.startswith('TABLE:')]
text+=['Global spectral minimality remains open in [9,11]. The eigenvalue bridge here is ordinary mathematics; the Lean endpoint is the unique group-inverse trace. Full rational matrices are in formal/Certificates.lean and sources/kirchhoff-review-r1/outputs/witness-exact.json.']
(D/'PROOF.md').write_text('\n\n'.join(text)+'\n')
files=[]
for n in ['formal','negative','checks','sources']:
 for f in (D/n).rglob('*'):
  if f.is_file() and f.suffix not in ['.olean','.ilean','.pyc','.zip']:files.append(f)
for n in ['replay.py','scripts/run.py','scripts/check_exact.py','scripts/safe_extract.py','paper/manuscript.json','paper/render.py','REPRODUCE.md','PROOF.md','statement-correspondence.md','input-hashes-before.json','TASK.txt']:files.append(D/n)
h={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(files))}
(D/'source-hashes.json').write_text(json.dumps(h,indent=2)+'\n')
files.append(D/'source-hashes.json')
with zipfile.ZipFile(D/'kirchhoff-source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(set(files)):z.write(p,str(p.relative_to(D)))
print('Source packet',len(set(files)),'files')
