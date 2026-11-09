from pathlib import Path
import hashlib,json,re
L=Path(__file__).resolve().parent
terms=['Gentner','Rautenbach','Butler','Graham','Tribonacci','Boesch','Beiter','Delta square','Zhuang','Gao','permutation numerical','Ugolini','zero forcing','marking coordinate','Macdonald intersection','uniformly most reliable','cyclotomic','product-one','small Davenport']
files=sorted({p for p in L.parent.glob('*/*') if p.is_file() and p.name in ['SCOUTING.md','SUMMARY.md','STATUS.md','discovery.md'] and p.parent!=L})
records=[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
(L/'history-bindings.json').write_text(json.dumps(records,indent=2))
out={s:[] for s in terms}
for p,r in zip(files,records):
 data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==r['sha256']
 for s in terms:
  lines=[x.strip() for x in data.decode(errors='replace').splitlines() if s.lower() in x.lower()]
  if lines:out[s].append({'path':str(p),'hits':lines})
(L/'dedup.json').write_text(json.dumps(out,indent=2))
for s,h in out.items():print(s,'FILES',len(h),'PATHS',','.join(Path(x['path']).parent.name for x in h))
