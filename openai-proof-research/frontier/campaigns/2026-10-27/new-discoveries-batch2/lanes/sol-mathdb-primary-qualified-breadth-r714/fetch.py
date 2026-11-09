import pathlib,urllib.request,json,hashlib,datetime,subprocess
P=pathlib.Path(__file__).parent;out=[]
for a in ['2406.09369v1','2412.03500v1','2404.01597v1']:
 url='https://arxiv.org/pdf/'+a;d=dict(url=url,version=a,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=35) as r:b=r.read(6000000);d['http']=r.status
  assert b.startswith(b'%PDF') and len(b)<6000000
  p=P/(a+'.pdf');p.write_bytes(b);d.update(pdf_sha256=hashlib.sha256(b).hexdigest(),pdf_size=len(b))
  # Commit PDF binding before invoking extraction.
  out.append(d);(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  t=P/(a+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=30)
  d.update(text_sha256=hashlib.sha256(t.read_bytes()).hexdigest(),text_size=t.stat().st_size)
 except Exception as e:
  d['failure']=str(e)
  if d not in out:out.append(d)
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
