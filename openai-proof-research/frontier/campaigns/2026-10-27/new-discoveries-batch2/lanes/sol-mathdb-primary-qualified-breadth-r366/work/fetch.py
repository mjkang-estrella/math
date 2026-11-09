from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,subprocess
R=Path(__file__).resolve().parents[1];(R/'sources').mkdir(exist_ok=True);out=[]
for tag,aid in [('hooks','1910.08895'),('spread','2407.18688'),('generating','hep-th/0009129'),('signature','2512.13450'),('queens','2406.06260')]:
 url='https://arxiv.org/pdf/'+aid
 row=dict(tag=tag,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),requested_version='current PDF; version unconfirmed')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as f:b=f.read(10000000);row.update(status=f.status,final_url=f.url)
  p=R/'sources'/(tag+'.pdf');p.write_bytes(b);row.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
  # Hash and record response BEFORE extraction. Fail closed for HTML/non-PDF/challenge.
  row['usable']=b.startswith(b'%PDF') and not any(x in b[:5000].lower() for x in [b'proof-of-work',b'captcha',b'anubis',b'cf-chl-',b'just a moment'])
  out.append(row);(R/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  if row['usable']:subprocess.run(['pdftotext','-layout',str(p),str(R/'work'/(tag+'.txt'))],check=True)
 except Exception as e:
  row.update(error=str(e),usable=False);out.append(row);(R/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(row),flush=True)
