from pathlib import Path
import re,json,urllib.request,urllib.error,datetime,hashlib,subprocess
L=Path(__file__).resolve().parent;es=[]
for p in sorted((L/'sources').glob('owr-*.html')):
 urls=re.findall(r'https://content.ems.press/[^"\s<>\\]+\.pdf',p.read_text());assert urls
 url=urls[0];e=dict(name=p.stem+'-pdf',url=url,version=p.stem,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   raw=r.read(16*1024*1024+1);assert len(raw)<=16*1024*1024 and raw.startswith(b'%PDF')
   out=p.with_suffix('.pdf');out.write_bytes(raw);out.with_suffix('.pdf.headers').write_text(str(r.headers));e.update(status=r.status,file=str(out.relative_to(L)),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
   subprocess.run(['pdftotext','-layout',str(out),str(out.with_suffix('.txt'))],check=True)
 except Exception as x:
  e.update(status='HOLD',error=str(x));es.append(e)
  if isinstance(x,urllib.error.HTTPError) and x.code in (403,429):break
  continue
 es.append(e);print(e['name'],e['status'],flush=True)
(L/'sources-owr.json').write_text(json.dumps(es,indent=2)+'\n')
