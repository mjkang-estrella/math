from pathlib import Path
import json,hashlib,subprocess,re
D=Path(__file__).resolve().parents[1];B=D.parent.parent;ids=json.loads((D/'reservation.json').read_text())['ids'];pat=r'\b('+('|'.join(map(str,ids)))+r')\b'
r=subprocess.run(['rg','-n','--max-columns','500','--max-columns-preview','-e',pat,str(B),'-g','*.md','-g','ledger.json','-g','results.json','-g','review.json'],capture_output=True,text=True)
lines=[l for l in r.stdout.splitlines() if '/expanded-corpus-r218/' not in l];(D/'logs/history-refined.txt').write_text('\n'.join(lines)+'\n')
paths=[D.parent/'ledger.json',B/'ledger.json',B/'prior-campaign-context.json'];out={}
for p in paths:
 if p.exists():
  data=p.read_bytes();x=json.loads(data);out[str(p)]={'sha256':hashlib.sha256(data).hexdigest(),'top_keys':list(x),'matched_reserved_records':[]}
  def walk(x):
   if isinstance(x,dict):
    if x.get('mathdb_id') in ids:out[str(p)]['matched_reserved_records'].append(x)
    for y in x.values():walk(y)
   elif isinstance(x,list):
    for y in x:walk(y)
  walk(x)
(D/'logs/ledger-read.json').write_text(json.dumps(out,indent=2));print('refined matches',len(lines));print('\n'.join(l[:500] for l in lines[:8]))
