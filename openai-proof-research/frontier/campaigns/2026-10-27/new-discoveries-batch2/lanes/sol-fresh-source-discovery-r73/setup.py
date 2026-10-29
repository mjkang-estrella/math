from pathlib import Path
import json,hashlib,datetime,re
r=Path(__file__).resolve().parent;b=r.parent.parent;repo=b.parents[3]
files=list(repo.rglob('*SUMMARY*'))+list(repo.rglob('*summary*'))
terms=['A390107','14010127','2511.08320','2601.11253','Tărnăuceanu','prime factorization of the binomial','He and Yuan','binomial coprimality']
rows=[]
for p in dict.fromkeys(files):
 if not p.is_file() or r in p.parents:continue
 try:t=p.read_text()
 except (UnicodeError,OSError):continue
 hits=[s for s in terms if s.lower() in t.lower()]
 rows.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':hits})
(r/'context-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows,'terms':terms},indent=2))
print('summary files searched',len(rows),'hits',[(x['path'],x['hits']) for x in rows if x['hits']])
