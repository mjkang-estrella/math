import pathlib,json,re,urllib.request,urllib.error,hashlib,datetime,subprocess
R=pathlib.Path(__file__).resolve().parent;log=[];blocked=set()
for p in sorted((R/'sources').glob('owr*.html')):
 s=p.read_text();m=re.search(r'name="citation_pdf_url" content="([^"]+)"',s)
 if not m:continue
 u=m[1];host=__import__('urllib.parse',fromlist=['urlparse']).urlparse(u).netloc
 if host in blocked:continue
 try:
  with urllib.request.urlopen(u,timeout=20) as r:data=r.read(16000000);final=r.url
  dest=p.with_suffix('.pdf');dest.write_bytes(data);subprocess.run(['pdftotext','-layout',str(dest),str(p.with_suffix('.txt'))],check=True)
  log.append({'file':str(dest.relative_to(R)),'url':u,'final_url':final,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'downloaded'})
 except Exception as e:
  log.append({'url':u,'status':'HOLD','error':str(e)})
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):blocked.add(host)
(R/'body-access.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(log,indent=2))
