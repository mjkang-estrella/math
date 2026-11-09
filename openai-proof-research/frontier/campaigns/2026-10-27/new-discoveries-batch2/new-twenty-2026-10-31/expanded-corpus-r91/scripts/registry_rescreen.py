import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];pat=re.compile(r'sylow|lindzey|eventown|even.?cycle.?intersect|singular.?famil|372630|372631',re.I);r=[]
for p in [D/'sources/omega-D5.json',D/'sources/omega-Problems.json',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']:
 x=json.loads(p.read_text());r.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':x.get('truncated'),'count':len(x['tree']),'matches':[a for a in x['tree'] if pat.search(a['path'])]})
(D/'outputs/registry-sylow-screen.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
