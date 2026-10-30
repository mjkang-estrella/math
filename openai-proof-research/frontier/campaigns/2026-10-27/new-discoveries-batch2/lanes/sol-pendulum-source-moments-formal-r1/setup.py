import pathlib,json,hashlib,shutil
R=pathlib.Path(__file__).resolve().parent
B=R.parent.parent
L=R.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
rows=[]
for rel in ['root-r166-preliminary-freeze-r1/review-freeze.json','root-pendulum-investment-adoption-r3/review-freeze.json']:
 p=L/rel
 for row in json.loads(p.read_text())['files']:
  q=pathlib.Path(row['path']);assert sha(q)==row['sha256'],str(q)
  rows.append(row)
(R/'originals-before.json').write_text(json.dumps(rows,indent=2)+'\n')
for d in ['formal','logs','inputs']: (R/d).mkdir(exist_ok=True)
old=L/'sol-renyi-deficit-source-formal-r2'
for n in ['guard.py','replay_guard.py','helper_guard.py','pins.json']:
 shutil.copyfile(old/n,R/n)
for rel in ['root-r166-preliminary-freeze-r1/review-freeze.json','root-pendulum-investment-adoption-r3/review-freeze.json','root-pendulum-investment-adoption-r3/DECISION.md','root-pendulum-investment-adoption-r3/INTERFACE.md','sol-pendulum-investment-review-r3/review.md','sol-pendulum-source-subsumption-review-r2/review.md','sol-fresh-source-discovery-r166/PROOF.md']:
 p=L/rel;shutil.copyfile(p,R/'inputs'/rel.replace('/','--'))
for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 p=B/n
 s=p.read_text()
 print(n,len(s),s[:180],s[-2000:])
for rel in ['sol-pendulum-investment-review-r3/review.md','sol-pendulum-source-subsumption-review-r2/review.md','sol-fresh-source-discovery-r166/PROOF.md']:
 print(rel,(L/rel).read_text())
print('verified frozen entries',len(rows))
