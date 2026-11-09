import json,pathlib,urllib.request,urllib.error,re,concurrent.futures,subprocess,hashlib,threading
O=pathlib.Path(__file__).parent;(O/'primary').mkdir(exist_ok=True); stop=threading.Event()
rs=json.loads((O/'selected-records.json').read_text()); logs=[]
def get(u,p):
 if stop.is_set():raise RuntimeError('host parked after denial')
 try:
  with urllib.request.urlopen(u,timeout=20) as f:b=f.read(12000000)
 except urllib.error.HTTPError as e:
  if e.code in [403,429]:stop.set()
  raise
 p.write_bytes(b)
 if b'cf-chl-' in b or b'Just a moment' in b:stop.set();raise RuntimeError('challenge; host parked')
 logs.append({'url':u,'file':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
 return b
fail=[]
def work(u):
 tag=u.rsplit('/',1)[1]
 try:
  b=get(u,O/'primary'/f'{tag}.html')
  links=re.findall(rb'href="([^"]+)"',b)
  links=[x.decode().replace('&amp;','&') for x in links if b'/content/serial-article-files/' in x]
  assert links,'no pdf link'
  v=urllib.parse.urljoin(u,links[0]); p=O/'primary'/f'{tag}.pdf';get(v,p)
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=15)
 except Exception as e:fail.append({'url':u,'error':str(e)})
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:list(ex.map(work,sorted(set(r['source_url'] for r in rs))))
(O/'primary-provenance.json').write_text(json.dumps(logs,indent=2)+'\n');(O/'fetch-failures.json').write_text(json.dumps(fail,indent=2)+'\n')
print('sources',len(logs),'failures',fail)
