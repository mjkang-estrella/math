from pathlib import Path
import json,re,urllib.request,urllib.error,subprocess,concurrent.futures,hashlib,datetime
R=Path(__file__).resolve().parent;(R/'sources').mkdir(exist_ok=True)
rows=json.loads((R/'records.json').read_text());urls=sorted(set(o['source_url'] for o in rows))
def get(url):
 out={'url':url,'accessed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};n=url.rsplit('/',1)[1]
 try:
  with urllib.request.urlopen(url,timeout=18) as f:b=f.read()
  (R/f'sources/{n}.html').write_bytes(b)
  p=re.search(rb'name="citation_pdf_url" content="([^"]+)"',b).group(1).decode();out['pdf_url']=p
  with urllib.request.urlopen(p,timeout=24) as f:b=f.read()
  assert b.startswith(b'%PDF')
  (R/f'sources/{n}.pdf').write_bytes(b)
  c=subprocess.run(['pdftotext','-layout',str(R/f'sources/{n}.pdf'),str(R/f'sources/{n}.txt')],capture_output=True)
  out.update(status='downloaded_not_yet_inspected',pdf_sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),extract_returncode=c.returncode)
 except Exception as e:out.update(status='HOLD',error=str(e))
 return out
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:out=list(ex.map(get,urls))
(R/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
