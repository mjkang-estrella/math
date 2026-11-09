from pathlib import Path
import hashlib,json,shutil
here=Path(__file__).resolve().parent
batch=here.parent.parent
candidate=here.parent/'sol-median-dynamics-breadth-depth-r1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
files=[p for p in candidate.iterdir() if p.is_file()]+list((candidate/'frozen').iterdir())
for p in files:
 if not p.is_file(): continue
 target=here/'frozen'/p.relative_to(candidate)
 target.parent.mkdir(parents=True,exist_ok=True)
 before=sha(p);shutil.copyfile(p,target);after=sha(p)
 assert before==after==sha(target)
 records.append(dict(original=str(p),copy=str(target.relative_to(here)),before=before,after=after))
for p in [batch/'AGENTS.md',batch/'ledger.json',batch/'prior-campaign-context.json',batch.parents[3]/'AGENTS.md']:
 if p.exists():
  target=here/'administrative'/p.name;target.parent.mkdir(exist_ok=True);shutil.copyfile(p,target)
(here/'freeze.json').write_text(json.dumps(records,indent=2))
print('Frozen',len(records),'scientific files before reading; administrative snapshots only.')
