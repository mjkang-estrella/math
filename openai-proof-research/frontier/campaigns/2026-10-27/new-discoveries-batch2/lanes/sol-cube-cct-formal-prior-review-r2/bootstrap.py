import pathlib, hashlib, json, shutil, tarfile
L=pathlib.Path(__file__).parent
B=L.parent.parent
S=L.parent/'sol-cube-cct-source-formal-r1'
P=L.parent/'sol-cube-cct-preliminary-review-r1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for base,names,dest in [(S,['SUMMARY.md','source-only.tar.gz','Audit.lean','audit01.log','audit_verify.py','lean_guard.py','pins.json','run.sh','source-manifest.json','package.py','provenance.json','FAILURES.md'],L/'frozen/source'),(P,['review.md'],L/'frozen/preliminary'),(B,['ledger.json','prior-campaign-context.json','AGENTS.md'],L/'administrative')]:
 dest.mkdir(parents=True,exist_ok=True)
 for n in names:
  p=base/n; q=dest/n; before=sha(p); shutil.copyfile(p,q); after=sha(p)
  assert before==after==sha(q)
  records.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=before))
assert sha(L/'frozen/source/source-only.tar.gz')=='ead8a07b9a339d55285f12e37f96fb6834a58007988160e8df8a8a864e3c595d'
(L/'freeze.json').write_text(json.dumps(records,indent=2))
with tarfile.open(L/'frozen/source/source-only.tar.gz') as t:
 for m in t.getmembers():
  assert not m.issym() and not m.islnk() and not pathlib.PurePosixPath(m.name).is_absolute() and '..' not in pathlib.PurePosixPath(m.name).parts
 t.extractall(L/'replay',filter='data')
for n in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/n).read_text()); print(n, 'keys', list(d)); print({k:v for k,v in d.items() if k in ['accepted_count','total_accepted_count','next_global_outcome_number','note']})
print('frozen',len(records))
