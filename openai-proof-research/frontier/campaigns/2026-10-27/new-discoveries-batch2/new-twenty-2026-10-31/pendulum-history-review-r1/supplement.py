from pathlib import Path
exec((Path(__file__).parent/'assess.py').read_text().split("head=fetch(")[0])
tracked=js(L/'additional-input-hashes.json');receipts=js(L/'http-receipts.json')
x=fetch('live-omega-default-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'); head=x['sha'] if x else None
print('default head',head,flush=True)
if head:
 for f in ['IncompleteBeta/Moment','IncompleteBeta/Result','IncompleteBetaShape/Kernel','IncompleteBetaShape/Result','EllipticTailExponent/Result']:
  url='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/D5/S3/Analytic/'+f+'.lean'
  # raw text handled separately (fetch expects JSON)
  t=datetime.datetime.now(datetime.timezone.utc).isoformat()
  try:
   with urllib.request.urlopen(url,timeout=15) as r:d=r.read(2**20);status=r.status
  except urllib.error.HTTPError as e:d=e.read();status=e.code
  n='current-'+f.replace('/','-')+'.lean';(L/n).write_bytes(d);receipts.append({'utc':t,'url':url,'status':status,'sha256':hashlib.sha256(d).hexdigest(),'bytes':len(d),'path':str(L/n)});print(n,status,len(d),flush=True)
# additional existing primary provenance
for f in ['retrievals.jsonl','body-coverage.json']:
 read(B/'lanes/sol-pendulum-source-subsumption-review-r2'/f)
for f in ['companion-registry-receipts.json','sources/trureturing-head.json','sources/AIM-head.json']:
 read(B/'new-twenty-2026-10-31/expanded-corpus-r33'/f)
save('http-receipts.json',receipts);save('additional-input-hashes.json',tracked)
