from pathlib import Path
import hashlib,json,datetime,shutil
lane=Path(__file__).resolve().parent
batch=lane.parent.parent
rows=[]
for name in ['sol-quantile-aggregation-preliminary-review-r1','sol-quantile-aggregation-full-r1']:
 for p in sorted((batch/'lanes'/name).rglob('*')):
  if p.is_file():
   rows.append({'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(lane/'freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'immutable reference binding; no scientific copies','files':rows},indent=2)+'\n')
(lane/'administrative').mkdir(exist_ok=True)
for p in [batch/'ledger.json',batch/'prior-campaign-context.json',batch/'AGENTS.md',batch.parents[3]/'AGENTS.md']:
 if p.is_file(): shutil.copyfile(p,lane/'administrative'/p.name)
print(json.dumps({'bound_files':len(rows),'bytes':sum(r['bytes'] for r in rows)}))
