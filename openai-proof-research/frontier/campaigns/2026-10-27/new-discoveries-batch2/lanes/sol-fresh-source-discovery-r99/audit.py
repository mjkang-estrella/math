from pathlib import Path
import re,json,hashlib,datetime
P=Path(__file__).resolve().parent
R=next(x for x in P.parents if x.name=='openai-proof-research')
terms=re.compile(r'super.?domina|super.?domatic|Kov.cs.{0,8}Nagy|368607|2505.24072|competition.number',re.I)
files=[];hits=[]
for f in R.rglob('*'):
 if not f.is_file() or P in f.parents:continue
 if not(any(t in f.name.lower() for t in ['summary','discovery','findings','proof','review','ledger']) and f.suffix.lower() in ['.md','.json','.txt']):continue
 b=f.read_bytes();files.append(dict(path=str(f.relative_to(R)),sha256=hashlib.sha256(b).hexdigest()))
 for i,l in enumerate(b.decode(errors='replace').splitlines(),1):
  if terms.search(l):hits.append(dict(path=str(f.relative_to(R)),line=i,text=l[:1500]))
(P/'duplicate-audit.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),terms=terms.pattern,files=files,hits=hits),indent=2))
print(len(files),'files',len(hits),'hits');print(json.dumps(hits,indent=2))
for fn in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((P.parent.parent/fn).read_text());print(fn,list(d));
 if fn=='ledger.json':print([(x['number'],x['title']) for x in d['accepted']])
