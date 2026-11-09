from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parents[1];ids=json.loads((L/'reservation.json').read_text())['ids'];pat=re.compile(r'\b('+'|'.join(map(str,ids))+r')\b');hits=[]
for p in L.parents[1].rglob('*'):
 if L in p.parents or not p.is_file() or p.name not in ['SUMMARY.md','CANDIDATE.md','results.json','ledger.json']:continue
 if p.stat().st_size>4000000:continue
 s=p.read_text(errors='replace')
 for i,line in enumerate(s.splitlines(),1):
  if pat.search(line):hits.append({'path':str(p),'line':i,'text':line[:1500]})
(L/'outputs/history-screen.json').write_text(json.dumps(hits,indent=2));print('history hits',len(hits));print(json.dumps(hits[:10],indent=2))
