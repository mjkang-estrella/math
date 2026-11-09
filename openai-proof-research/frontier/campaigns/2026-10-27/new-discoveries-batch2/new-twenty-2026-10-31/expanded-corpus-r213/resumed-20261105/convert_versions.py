import pathlib,json,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parents[1];O=L/'resumed-20261105';rows=[]
for p in (L/'receipts').glob('*.json'):
 r=json.loads(p.read_text());b=L/'receipts'/r.get('body_file','MISSING')
 if not b.exists():continue
 assert hashlib.sha256(b.read_bytes()).hexdigest()==r['sha256']
 if r['url'].startswith('https://arxiv.org/pdf/'):
  a=r['url'].rsplit('/',1)[1]
  if 'v' in a and r['status']==200:subprocess.run(['pdftotext','-layout',str(b),str(O/'text'/(a+'.txt'))],check=True);rows.append({'url':r['url'],'sha256':r['sha256'],'receipt':str(p.relative_to(L))})
(O/'version-pdfs.json').write_text(json.dumps(rows,indent=2));print(len(rows))
