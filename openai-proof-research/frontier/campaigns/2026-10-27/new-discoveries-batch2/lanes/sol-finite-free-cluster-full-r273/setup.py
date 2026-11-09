from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent; B=L.parent.parent; R=L.parent/'sol-wide-new-source-mechanisms-r266'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
(L/'admin').mkdir(exist_ok=True);(L/'frozen').mkdir(exist_ok=True)
for p in [B/'ledger.json',B/'prior-campaign-context.json',B/'AGENTS.md',B.parents[3]/'AGENTS.md']:
 if p.exists():shutil.copyfile(p,L/'admin'/p.name.replace('AGENTS','batch-AGENTS' if p.parent==B else 'ancestor-AGENTS'))
names=['discovery.md','SCOUTING.md','SUMMARY.md','FAILURES.md','provenance.json','finite-free-prior.json','history-hits.json','selected-chronology.json','science/1811.06382v1.pdf','science/1811.06382v1.txt','science/finite-free-prior.xml']
rows=[]
for name in names:
 p=R/name;q=L/'frozen'/name.replace('/','--');h=sha(p);shutil.copyfile(p,q);assert sha(p)==sha(q)==h;rows.append(dict(original=str(p),copy=str(q),sha256=h))
(L/'source-bindings.json').write_text(json.dumps(rows,indent=2));print('Frozen and verified',len(rows),'inputs')
print('counts', {k:json.loads((B/'ledger.json').read_text())[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']})
