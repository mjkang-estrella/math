from pathlib import Path
import re,json,hashlib
L=Path(__file__).resolve().parent;R=L.parent.parent.parent
pat=re.compile(r'\b(?:334806|334903|339518|339814|342276|342942|358939|361905|365265|367822|368829|371946|329594|329617|329705|329726|329788|329836|329850|329995)\b|queen.{0,40}(?:reject|exclud|protect)|polynomial.{0,30}positivity|graph.family',re.I)
out=[]
for p in R.rglob('*'):
 if not p.is_file() or L in p.parents or p.suffix not in ['.md','.json','.txt']:continue
 if not any(w in p.name.lower() for w in ['result','summary','reject','review','status','ledger','context','hold']):continue
 if p.stat().st_size>1500000:continue
 try:s=p.read_text()
 except Exception:continue
 hits=[{'line':n,'text':z[:2000]} for n,z in enumerate(s.splitlines(),1) if pat.search(z)]
 if hits:out.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'matches':hits})
(L/'history-wide.json').write_text(json.dumps(out,indent=2));print('files',len(out))
for x in out:
 if any(re.search(r'\b(?:339814|361905|329705|329726|358939)\b',h['text']) for h in x['matches']):print(json.dumps(x)[:3500])
