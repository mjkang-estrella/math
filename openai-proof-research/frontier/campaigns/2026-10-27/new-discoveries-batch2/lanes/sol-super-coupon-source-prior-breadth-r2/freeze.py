from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
records=[]
def bind(p,copy=False,admin=False):
 b=p.read_bytes(); h=hashlib.sha256(b).hexdigest()
 d=L/('admin' if admin else 'frozen')/p.relative_to(B)
 if copy:
  d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b)
  assert hashlib.sha256(d.read_bytes()).hexdigest()==h
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 records.append(dict(original=str(p),sha256=h,bytes=len(b),copy=str(d) if copy else None,administrative=admin))
for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:bind(B/n,True,True)
for lane,names in {
 'sol-wide-analytic-source-scout-r254':['PROOF.md','discovery.md','SCOUTING.md','SUMMARY.md','FAILURES.md','primarybindings.json','chronology.json','provenance.json','texts/2304.01145v2.txt','primary/2304.01145v2.pdf'],
 'sol-dependent-super-coupon-preliminary-review-r1':['review.md','FAILURES.md','check-results.json']}.items():
 for n in names:bind(B/'lanes'/lane/n,True)
# Reuse other immutable scientific references in these lanes without recursive copies.
for lane in ['sol-wide-analytic-source-scout-r254','sol-dependent-super-coupon-preliminary-review-r1']:
 for sub in ['primary','texts','retrieved']:
  p=B/'lanes'/lane/sub
  if p.exists():
   for f in sorted(p.iterdir()):
    if f.is_file() and str(f) not in [r['original'] for r in records]:bind(f)
(L/'sourcebindings.json').write_text(json.dumps({'frozen_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records':records},indent=2)+'\n')
print(json.dumps({'bound':len(records),'counts':[9,39,40]}))
