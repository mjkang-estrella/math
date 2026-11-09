import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parents[1]; O=L/'resumed-20261105'; out={}
for p in (L/'receipts').glob('*.json'):
 r=json.loads(p.read_text());
 if r.get('status')!=200:continue
 b=L/'receipts'/r['body_file'];assert hashlib.sha256(b.read_bytes()).hexdigest()==r['sha256']
 if r['url'].startswith('https://arxiv.org/abs/'):
  s=b.read_text(); a=r['url'].rsplit('/',1)[1]; versions=re.findall(r'\[v(\d+)\].{0,180}',s); out[a]={'receipt':str(p.relative_to(L)),'sha256':r['sha256'],'versions':versions,'history_text':re.sub('<[^>]*>',' ',s[s.find('Submission history'):s.find('Submission history')+4000])}
 if r['url'].startswith('https://arxiv.org/pdf/') and r['url'].rsplit('/',1)[1] in ['1908.04654','2206.08914']:
  import subprocess
  subprocess.run(['pdftotext','-layout',str(b),str(O/'text'/(r['url'].rsplit('/',1)[1]+'.txt'))],check=True)
(O/'versions.json').write_text(json.dumps(out,indent=2));print('\n'.join(k+' '+str(v['versions']) for k,v in out.items()))
