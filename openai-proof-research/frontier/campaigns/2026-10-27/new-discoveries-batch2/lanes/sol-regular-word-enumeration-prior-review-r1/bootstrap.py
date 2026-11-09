from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-wide-independent-scout-r249'
rows=[]
def freeze(p,rel,admin=False):
 b=p.read_bytes(); h=hashlib.sha256(b).hexdigest(); q=L/('administrative' if admin else 'frozen')/rel
 q.parent.mkdir(parents=True,exist_ok=True); q.write_bytes(b)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,administrative=admin))
for name in ['ledger.json','prior-campaign-context.json','AGENTS.md']:freeze(B/name,Path(name),True)
for name in ['PROOF.md','SUMMARY.md','SCOUTING.md','FAILURES.md','failures.jsonl','sources.jsonl','chronology.json','provenance.json','discovery.md','freeze.json','verification-receipt.json']:
 freeze(S/name,Path(name))
for folder in ['frozen-sources','texts']:
 for p in sorted((S/folder).iterdir()):
  if p.is_file():freeze(p,Path(folder)/p.name)
(L/'freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'inputs':rows},indent=2)+'\n')
print('Frozen',len(rows),'files')
print('\n'.join(str(p.relative_to(L)) for p in (L/'frozen'/'texts').iterdir()))
