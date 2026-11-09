from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[1]
# Final metadata annotation: treat unexpected PoW marker as failed search, not prior art.
p=R/'successor-provenance.json';v=json.loads(p.read_text())
for e in v:
 if e['name'].endswith('-search'):e.update(usable_for_novelty=False,access_limitation='HTTP200 contains PoWConfig/PoWChallengeSolver script markers; not executed; host stopped after inspection; no retry')
p.write_text(json.dumps(v,indent=2)+'\n')
files=[]
for p in sorted(R.rglob('*')):
 if p.is_file() and p.relative_to(R).as_posix() not in {'manifest.json','verification-receipt.json'}:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(R/'manifest.json').write_text(json.dumps(dict(files=files),indent=2)+'\n')
print('sealed',len(files),'files')
