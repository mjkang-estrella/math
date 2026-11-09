from fetch import D,get
import json,re,hashlib
h=json.load(open(D/'sources/omega-tree.json'))
for x in h['tree']:
 if x['path'] in ['D5','Problems']:print(get(('omega-'+x['path']+'.json',x['url']+'?recursive=1')))
terms=['comb','burning','ornament','overcolor','overcolour','372995','373367','373402','Mobius','Möbius','Rota','lengthregular']
r={}
for p in [D/'sources/omega-D5.json',D/'sources/omega-Problems.json',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']:
 d=json.load(open(p));paths=[x['path'] for x in d.get('tree',[])];matches=[x for x in paths if any(t.lower() in x.lower() for t in terms)]
 r[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':d.get('truncated'),'entries':len(paths),'matches':matches}
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
