from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parents[1];r=[]
for p in sorted((D/'sources').glob('*.receipt.json')):
 x=json.loads(p.read_text());body=p.with_name(p.name.replace('.receipt.json','.body'))
 if body.exists():
  h=hashlib.sha256(body.read_bytes()).hexdigest();assert h==x['sha256'];r.append(dict(receipt=p.name,body=body.name,sha256=h,url=x.get('url'),status='PASS'))
(D/'source-receipt-check.json').write_text(json.dumps(r,indent=2)+'\n')
print('Source receipts verified:',len(r))
