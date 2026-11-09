import pathlib,json,re,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1]
pat=re.compile(r'isolation game|happy edge|parking edge|gleeful|temperley|corona|bipartite.swapp|hyper.zagreb|fibonacci.*path|path.*fibonacci|Cruickshank|Sober[oó]n|369233|369627|369861',re.I)
out={}
for p in [D/'sources/pool-projects.yml',D/'sources/omega-conjectures.html']:
 if p.exists():
  s=p.read_text();out[p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'matches':[s[max(0,m.start()-180):m.end()+280] for m in pat.finditer(s)]}
for name in ['ledger','batch-ledger','prior']:
 s=(D/'logs'/(name+'.json')).read_text();out[name]={'bytes':len(s),'family_matches':[s[max(0,m.start()-100):m.end()+100] for m in re.finditer(r'nut graph|circulant|Latin|stack.sort|369935|369934',s,re.I)][:40]}
(D/'registry-and-family-screen.json').write_text(json.dumps(out,indent=2));print({k:len(v.get('matches',v.get('family_matches',[]))) for k,v in out.items()})
