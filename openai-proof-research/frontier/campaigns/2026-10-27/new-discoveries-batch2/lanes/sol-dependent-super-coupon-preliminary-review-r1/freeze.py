from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-wide-analytic-source-scout-r254'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
out=[]
names=['SUMMARY.md','PROOF.md','discovery.md','FAILURES.md','SCOUTING.md','chronology.json','provenance.json','primarybindings.json','retrieval-bindings.json','reopened-bindings.json','method-excerpts.json','finalmanifest.json','verification-receipt.json']
paths=[S/x for x in names]+list((S/'primary').glob('*'))+list((S/'texts').glob('*'))
for p in paths:
 if not p.is_file():continue
 rel=p.relative_to(S);q=L/'frozen'/rel;q.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p);shutil.copyfile(p,q)
 assert sha(p)==h==sha(q)
 out.append(dict(original=str(p),copy=str(q),sha256=h,bytes=p.stat().st_size))
for p in [B/'ledger.json',B/'prior-campaign-context.json',B/'AGENTS.md',B.parents[3]/'AGENTS.md']:
 if p.is_file():
  q=L/'administrative'/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
(L/'bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scientific':out,'administrative':'snapshots only; not scientific invariance assertions'},indent=2)+'\n')
print('Frozen',len(out),'scientific/evidence files; original/copy hashes matched before reading.')
