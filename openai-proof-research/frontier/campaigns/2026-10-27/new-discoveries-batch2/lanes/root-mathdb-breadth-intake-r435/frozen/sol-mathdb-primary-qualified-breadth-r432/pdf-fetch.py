import urllib.request,pathlib,json,re,hashlib,subprocess
O=pathlib.Path(__file__).resolve().parent;events=json.loads((O/'source-provenance.json').read_text())
extra={'union-free':'https://math.mit.edu/~fox/paper-union-free.pdf','hultman':'https://sites.math.washington.edu/~billey/japan/references/hultman.pdf'}
urls={p.stem:re.search(r'name="citation_pdf_url" content="([^"]+)"',p.read_text())[1] for p in (O/'sources').glob('*.html')};urls.update(extra)
for key,url in urls.items():
 try:
  with urllib.request.urlopen(url,timeout=20) as r:b=r.read();final=r.url
  assert b.startswith(b'%PDF');p=O/'sources'/(key+'.pdf');p.write_bytes(b)
  events.append({'url':url,'final_url':final,'file':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'kind':'primary PDF; not automatic proof inspection'})
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  print(key,len(b),flush=True)
 except Exception as e:
  events.append({'url':url,'failure':repr(e),'retry':False});print(repr(e),flush=True)
  if getattr(e,'code',None) in [403,429]:break
(O/'source-provenance.json').write_text(json.dumps(events,indent=2)+'\n')
