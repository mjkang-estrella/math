from pathlib import Path
import hashlib,json,shutil,zipfile,io
L=Path(__file__).parent; P=L.parent/'sol-four-attractor-preliminary-review-r1'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];(L/'primary').mkdir(exist_ok=True)
for n in ['dolce.txt','2012.06840v6.extracted.txt','2602.16152v3.extracted.txt','2610.10950v1.extracted.txt']:
 p=P/n;q=L/'primary'/n;b=h(p);shutil.copyfile(p,q);assert b==h(p)==h(q)
 rows.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':b})
(L/'primary-freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
for level in [6,9]:
 with zipfile.ZipFile(L/'source-only.zip') as z:
  b=io.BytesIO()
  with zipfile.ZipFile(b,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=level) as out:
   for n in z.namelist():out.writestr(z.getinfo(n), (L/'extracted'/n).read_bytes())
  digest=hashlib.sha256(b.getvalue()).hexdigest()
  print('rebuild',level,digest)
  if digest==h(L/'source-only.zip'):
   (L/'archive-rebuild.json').write_text(json.dumps({'sha256':digest,'match':True,'compression':level,'metadata':'original ZipInfo','members':len(z.namelist())},indent=2)+'\n');break
else:raise AssertionError('no matching deterministic rebuild')
for n in ['ledger.json','prior-campaign-context.json']:
 obj=json.loads((L/n).read_text());print(n,'fully parsed',len(obj))
print(json.dumps(rows,indent=2))
