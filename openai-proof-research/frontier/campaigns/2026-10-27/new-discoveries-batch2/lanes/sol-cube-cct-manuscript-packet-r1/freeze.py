from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
admin=['AGENTS.md','ledger.json','prior-campaign-context.json']
for name in admin:
 p=B/name;q=L/'administrative'/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
rels=['sol-wide-algebra-scout-r222/PROOF.md','sol-cube-cct-preliminary-review-r1/review.md','sol-cube-cct-source-formal-r1/source-only.tar.gz','sol-cube-cct-source-formal-r1/SUMMARY.md','sol-cube-cct-formal-prior-review-r2/review.md','root-cube-cct-extracted-replay-r1/ROOT-REPLAY-RECEIPT.json']
for lane,sub in [('sol-cube-cct-preliminary-review-r1','primary'),('sol-cube-cct-formal-prior-review-r2','prior')]:
 rels += [str(p.relative_to(B/'lanes')) for p in (B/'lanes'/lane/sub).rglob('*') if p.is_file()]
records=[]
for rel in rels:
 p=B/'lanes'/rel;q=L/'frozen'/rel;q.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p);shutil.copyfile(p,q);assert sha(p)==sha(q)==h
 records.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':h})
assert next(r['sha256'] for r in records if r['copy'].endswith('source-only.tar.gz'))=='ead8a07b9a339d55285f12e37f96fb6834a58007988160e8df8a8a864e3c595d'
(L/'freeze.json').write_text(json.dumps(records,indent=2)+'\n')
print('Frozen',len(records),'scientific inputs; administrative snapshots separate.')
