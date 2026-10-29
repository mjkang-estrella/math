import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2);resource.setrlimit(resource.RLIMIT_CPU,(15,15));signal.alarm(25)
import json,hashlib,re,datetime
from pathlib import Path
b=Path(__file__).parent;old=b.parent/'sol-fresh-geometry-probability-r24';base=b.parents[1]
p=json.loads((old/'provenance.json').read_text()); recorded={Path(a['path']).name:a['sha256'] for a in p['artifacts']}
files=['coverage.json','registry-screen.json','discovery.md','check.py','sources/selection-v2.html','sources/selection-v2.txt','sources/volume.txt','sources/positive-bases.txt','sources/aim-steinitz.md','sources/openai-regression.tex','sources/openai-posterior.tex','sources/omega-D5-current-tree.json','sources/omega-Problems-current-tree.json','sources/openai-openai-preprints-tree.json','sources/count-count-full-tree.json','sources/aim-verified-complete-tree.json']
records=[]
for name in files:
 f=old/name;h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==recorded[f.name],name
 z=dict(path=str(f.resolve()),sha256=h,bytes=f.stat().st_size,verified_against=str((old/'provenance.json').resolve()))
 if 'tree.json' in name:
  t=json.loads(f.read_text());assert not t.get('truncated',False);z.update(entries=len(t['tree']),tree_sha=t['sha'],truncated=False)
 records.append(z)
ledger=json.loads((base/'ledger.json').read_text());assert ledger['accepted_count']==5 and ledger['total_accepted_count']==35
for name in ['AGENTS.md','ledger.json','NEXT.md','prior-campaign-context.json']:
 f=base/name;records.append(dict(path=str(f.resolve()),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size))
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),credit=0,accepted_counts=[5,35],inputs=records,current_registry_observation='Inherited live heads and complete subtree observations at 2026-10-29 09:05 UTC; rehashed here, not claimed refreshed at this run. GitHub API not retried after known403.',gaps=['No registry head update after09:05; no full-text whole-registry clearance.','AIM saved complete tree matches09:05 observed head; inherited403 preserved.','Steinitz nearest OpenAI manuscript body not additionally fetched; no absence claim.'])
(b/'input-reconciliation.json').write_text(json.dumps(out,indent=2));print('PASS',len(records),'verified inputs')
