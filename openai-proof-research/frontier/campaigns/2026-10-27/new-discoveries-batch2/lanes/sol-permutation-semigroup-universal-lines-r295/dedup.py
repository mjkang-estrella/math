from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
terms=['Bhattacharya','Friedland','Peled','Milman','strongly complemented','planar Turán','planar Turan','Khanin','Krikorian','Donkin','Jantzen','matching Kneser','Alishahi','Laptev','Safronov','HK-conjecture','Matui','Deeley']
rows=[];hits={t:[] for t in terms}
for p in sorted(L.parent.glob('*/*')):
 if p.parent==L or p.name not in ['SUMMARY.md','STATUS.md','SCOUTING.md','discovery.md']:continue
 data=p.read_bytes();h=hashlib.sha256(data).hexdigest()
 rows.append(dict(original=str(p),sha256=h,size=len(data)))
 # Bind before inspection, verify after. Administrative compact summaries only.
 for t in terms:
  ss=[s for s in data.decode(errors='replace').splitlines() if t.casefold() in s.casefold()]
  if ss:hits[t].append(dict(path=str(p),lines=ss))
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
(L/'history-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
(L/'dedup.json').write_text(json.dumps(hits,indent=2)+'\n')
for t,v in hits.items():print(t,len(v),[Path(x['path']).parent.name for x in v][:8])
