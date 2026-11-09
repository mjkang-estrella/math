import pathlib,json,urllib.request,urllib.error,hashlib,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent;(P/'sources').mkdir(exist_ok=True);log=[]
for aid in ['2608.15992v1','2608.19024v1','2608.26772v1','2609.04122v1']:
 url='https://arxiv.org/pdf/'+aid;entry=dict(url=url,version=aid,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearchScreen/1.0'}),timeout=30) as r:b=r.read();entry['http_status']=r.status;entry['final_url']=r.url
  path=P/'sources'/(aid+'.pdf');path.write_bytes(b);entry.update(pdf_path=str(path),pdf_sha256=hashlib.sha256(b).hexdigest(),pdf_size=len(b))
  (P/'source-provenance.json').write_text(json.dumps(log+[entry],indent=2)+'\n')
  if b.startswith(b'%PDF'):
   out=path.with_suffix('.txt');p=subprocess.run(['pdftotext','-layout',str(path),str(out)],capture_output=True);entry['extraction_exit']=p.returncode;entry['extraction_stderr']=p.stderr.decode(errors='replace')
   if out.exists():t=out.read_bytes();entry.update(text_path=str(out),text_sha256=hashlib.sha256(t).hexdigest(),text_size=len(t))
 except Exception as e:
  entry['error']=str(e);entry['http_status']=getattr(e,'code',None)
 log.append(entry);(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
 if entry.get('http_status') in [403,429]:break
print(json.dumps(log,indent=2))
