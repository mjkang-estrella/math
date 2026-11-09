import json,pathlib,hashlib,re
p=pathlib.Path(__file__).resolve().parent;c=p.parent;h=lambda x:hashlib.sha256(x).hexdigest()
files=[c/'fresh-corpus-r10/sources/registry-preprints.json',c/'staller-parent-final-r1/omega-D5-correct.json',c/'staller-parent-final-r1/omega-Problems-correct.json']
a=[]
for f in files:
 d=json.loads(f.read_bytes());paths=[x['path'] for x in d['tree']];matches=[x for x in paths if re.search('kneser|chebyshev|beloch|crown|likelihood|lineab|impropriety|complementary',x,re.I)];a.append({'file':str(f),'sha256':h(f.read_bytes()),'tree_sha':d.get('sha'),'truncated':d.get('truncated'),'entries':len(paths),'matches':matches})
r={'utc':'2026-11-01','live_heads':{n:json.loads((p/'sources'/f'{n}-head.json').read_text())['sha'] for n in ['openai','omega']},'scope':'Complete cached preprints and Omega D5/Problems paths reused under unchanged live HEAD; path screen only, bodies of matches unread. No global novelty clearance.','screens':a};(p/'registry-screen.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
