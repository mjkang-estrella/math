from pathlib import Path
import json,hashlib,re
L=Path(__file__).resolve().parent; B=L.parent.parent; O=L.parent/'sol-wide-specialist-arithmetic-scout-r274'
refs=json.loads((L/'source-bindings.json').read_text())
def bind(p):
 h=hashlib.sha256(p.read_bytes()).hexdigest();refs.append(dict(path=str(p),sha256=h,immutable_reference=True));return p.read_text(errors='replace')
hits=[]
pat=re.compile(r'canonical.{0,30}reduction|2003\.05391|Problem\s*21|Question\s*4\.4|m\s*\+\s*F\s*[-−]\s*f|Moscariello|pseudo.Frobenius',re.I)
for d in sorted(L.parent.iterdir()):
 if not d.is_dir() or d==L:continue
 for name in ['discovery.md','SCOUTING.md','SUMMARY.md','DISCOVERY.md']:
  p=d/name
  if p.is_file() and p.stat().st_size<200000:
   s=bind(p)
   excerpt=[s[max(0,m.start()-200):min(len(s),m.end()+500)] for m in pat.finditer(s)]
   if excerpt:hits.append(dict(path=str(p),excerpts=excerpt[:12]))
(L/'history-semantic.json').write_text(json.dumps(hits,indent=2))
(L/'source-bindings.json').write_text(json.dumps(refs,indent=2))
print('HISTORY',json.dumps(hits,indent=2)[:25000])
for n in ['near-original.txt','near-five.txt']:
 s=(O/'sources'/n).read_text();print('\nBODY',n,'\n',s[:70000])
for n in ['source-receipts.json','access.jsonl']:
 s=(O/n).read_text();print('\nMETA',n,'\n',s[:22000])
