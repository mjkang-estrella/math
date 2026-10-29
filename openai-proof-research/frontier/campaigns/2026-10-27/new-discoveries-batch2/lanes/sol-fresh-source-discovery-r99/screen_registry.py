from pathlib import Path
import re,json,hashlib
P=Path(__file__).resolve().parent;B=P.parent
terms=re.compile(r'super.?dominat|super.?domatic|Kov.cs|2305.05632|2505.24072|1705.00928|affine.*intersect|intersect.*affine|avoider|Vizing',re.I)
files=[B/'root-edge-irregulator-final-freeze-r1'/x for x in ['omega-tree.txt','openai-tree.txt','openai-CONTENTS.md','CURRENT-REGISTRIES.json']]
files+=list((P/'sources').glob('omega-delta-body-*'))
files+=[P/'sources/omega-delta.json']
r=[]
for f in files:
 b=f.read_bytes();hits=[dict(line=i,text=l[:1400]) for i,l in enumerate(b.decode(errors='replace').splitlines(),1) if terms.search(l)]
 r.append(dict(file=str(f),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),hits=hits))
(P/'registry-screen.json').write_text(json.dumps(r,indent=2));print(json.dumps([x for x in r if x['hits']],indent=2)[:14000])
