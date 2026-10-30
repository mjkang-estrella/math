from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
r=json.loads((P/'verification-receipt.json').read_text());assert r['status']=='PASS' and r['combined_actual_declarations']==139
paths=[P/n for n in ['Result.lean','combined-actual-declarations.json','combined-dependency-hashes.json','verification-receipt.json','root-replay.log','assembly.log','review-freeze.json','assemble.py','prepare.py']]
paths += [P.parent/'root-pendulum-convex-series-adoption-r2'/n for n in ['review-freeze.json','verification-receipt.json','DECISION.md']]
rows=[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in paths]
(P/'assembly-freeze.json').write_text(json.dumps({'files':rows},indent=2)+'\n');print('Assembly freeze PASS',len(rows))
