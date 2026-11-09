from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
root=L.parents[5]
# Administrative snapshots are explicitly not immutable scientific dependencies.
p=root/'AGENTS.md'
if p.exists():(L/'administrative'/'ancestor-AGENTS.md').write_bytes(p.read_bytes())
ledger=json.loads((L/'administrative'/'ledger.json').read_text())
prior=json.loads((L/'administrative'/'prior-campaign-context.json').read_text())
print(json.dumps({'counts':{k:ledger.get(k) for k in ['accepted_count','total_accepted_count','next_global_outcome_number']},'prior_accepted':[x.get('title') for x in prior['accepted']]}))
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']:
  rows.append({'path':str(p.relative_to(L)),'sha256':h(p),'bytes':p.stat().st_size})
(L/'manifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows},indent=2)+'\n')
print('manifest entries',len(rows))
