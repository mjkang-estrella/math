from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
R=Path(__file__).resolve().parents[1];out=[]
urls=[('hooks-successor','https://arxiv.org/pdf/2010.11834'),('signature-successor','https://arxiv.org/pdf/2602.16159'),('generating-successor','https://intlpress.com/api/bgcloud-front/resource/pdf/volume/1806606154140643330-1806606154140643330-b7a8d84a37f099ef8cf04ec49f10670a.pdf')]
for tag,url in urls:
 row=dict(tag=tag,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(10000000);row.update(status=f.status,final_url=f.url)
  p=R/'sources'/(tag+'.pdf');p.write_bytes(b);row.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
  row['usable']=b.startswith(b'%PDF') and not any(x in b[:5000].lower() for x in [b'proof-of-work',b'captcha',b'anubis',b'cf-chl-',b'just a moment'])
  out.append(row);(R/'successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  if row['usable']:subprocess.run(['pdftotext','-layout',str(p),str(R/'work'/(tag+'.txt'))],check=True)
 except Exception as e:row.update(error=str(e),usable=False);out.append(row);(R/'successor-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(row),flush=True)
