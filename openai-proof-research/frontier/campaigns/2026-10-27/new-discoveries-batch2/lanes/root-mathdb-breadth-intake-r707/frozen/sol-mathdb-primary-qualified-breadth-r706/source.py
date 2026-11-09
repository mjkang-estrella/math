from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
P=Path(__file__).resolve().parent
out=[]
for a in ['2001.08931v1','2003.05935v1','2102.04418v1','2104.10755v1','2103.02034v1','2105.01363v1']:
 u='https://arxiv.org/pdf/'+a
 r={'url':u,'version':a,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mozilla/5.0'}),timeout=30) as f:b=f.read();r['final_url']=f.url
  assert b.startswith(b'%PDF')
  p=P/(a+'.pdf');p.write_bytes(b);r.update(pdf_sha256=hashlib.sha256(b).hexdigest(),pdf_size=len(b),pdf_bound_before_extraction=True)
  (P/'source-provenance.json').write_text(json.dumps(out+[r],indent=2)+'\n')
  t=P/(a+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);d=t.read_bytes();r.update(text_sha256=hashlib.sha256(d).hexdigest(),text_size=len(d),text_bound_before_reading=True)
 except Exception as e:r['failure']=str(e)
 out.append(r);(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
