"""Re-extract exact raw lines and provenance. Run from anywhere; writes only lane."""
from pathlib import Path
import json,hashlib,subprocess,re
L=Path(__file__).resolve().parents[1];B=L.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
ids=set(json.loads((L/'reservation.json').read_text())['ids']);out=[]
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 h=sha(p.read_bytes())
 for line,raw in enumerate(p.open('rb'),1):
  d=json.loads(raw);i=d.get('mathdb_id',d.get('id'))
  if i in ids:
   (L/f'sources/{i}.jsonl').write_bytes(raw);out.append({'id':i,'chunk':str(p),'line':line,'chunk_sha256':h,'raw_sha256':sha(raw),'statement_sha256':sha(d['statement'].encode()),'statement_hash_encoding':'UTF-8 decoded statement, no appended newline'})
assert len(out)==20
(L/'outputs/provenance.json').write_text(json.dumps(out,indent=2)+'\n')
patterns=[str(i) for i in ids]+[json.loads((L/f'sources/{i}.jsonl').read_text())['title'] for i in ids]
args=['rg','-n','-F','--glob','*.md','--glob','results.json','--glob','*disposition*.json']
for s in patterns:args+=['-e',s]
r=subprocess.run(args+[str(B)],capture_output=True,text=True)
lines=[x for x in r.stdout.splitlines() if '/expanded-corpus-r86/' not in x]
(L/'outputs/history-matches.txt').write_text('\n'.join(lines)+'\n')
# Compact read-only input receipts, preserving accepted/excluded families for audit.
rec=[]
for p in [B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json']:
 d=json.loads(p.read_text());rec.append({'file':str(p),'sha256':sha(p.read_bytes()),'keys':list(d),'accepted':d.get('accepted',[]),'excluded':d.get('excluded',[]),'candidates':d.get('candidates',[])})
(L/'outputs/inherited-families.json').write_text(json.dumps(rec,indent=2)+'\n')
print('20 exact lines, statement hashes, historical ID/title matches and inherited family receipts saved.')
