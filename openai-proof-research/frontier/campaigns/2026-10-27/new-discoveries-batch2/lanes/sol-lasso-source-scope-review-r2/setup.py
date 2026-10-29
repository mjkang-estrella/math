import pathlib,json,hashlib,shutil,datetime,re
out=pathlib.Path(__file__).resolve().parent
batch=out.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
freeze=batch/'lanes/root-lasso-review-freeze-r1/review-freeze.json'
f=json.loads(freeze.read_text()); src=pathlib.Path(f['source_lane'])
result={}
for name,h in f['files'].items():
 p=src/name; d=out/'candidate-copy'/name; d.parent.mkdir(parents=True,exist_ok=True)
 result[name]={'expected':h,'original':sha(p)}; shutil.copyfile(p,d); result[name]['copy']=sha(d)
assert all(v['expected']==v['original']==v['copy'] for v in result.values())
(out/'before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':result},indent=2))
receipt=[]
for p in [batch/'ledger.json',batch/'NEXT.md',batch/'prior-campaign-context.json',batch.parent.parent.parent.parent/'sources/CONTENTS.md']:
 if not p.exists():continue
 text=p.read_text(); receipt.append({'path':str(p),'sha256':sha(p),'bytes':len(p.read_bytes()),'lines':len(text.splitlines()),'lasso_lines':[s for s in text.splitlines() if re.search(r'lasso|r79|Stallrich',s,re.I)]})
(out/'context-receipts.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt,indent=2))
pre=batch/'lanes/sol-lasso-max-preliminary-review-r1'
for name in ['review.md','provenance.json','http-provenance.json','checker.py','checker-results.json','before.json','after.json','registry-screen.json']:
 d=out/'preliminary-evidence'/name; d.parent.mkdir(exist_ok=True);shutil.copyfile(pre/name,d)
print('49 frozen files verified and copied')
