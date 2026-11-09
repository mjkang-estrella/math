import pathlib,json,hashlib,urllib.request,datetime,subprocess,sys
L=pathlib.Path(__file__).resolve().parent
def sha(d): return hashlib.sha256(d).hexdigest()
def freeze(p):
 d=p.read_bytes(); rec={'path':str(p.resolve()),'sha256':sha(d),'bytes':len(d),'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return d
def fetch(name,url):
 p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 rec={'url':url,'time':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'AcademicSourceCheck/1.0'}),timeout=25) as r:
   d=r.read(12000000); rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  if any(x in d[:20000].lower() for x in [b'captcha',b'cf-chl-',b'just a moment']):raise RuntimeError('challenge; stop route')
  p.write_bytes(d);rec.update(sha256=sha(d),bytes=len(d));freeze(p)
  if d.startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=30);freeze(p.with_suffix('.txt'))
 except Exception as e:rec['failure']=repr(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
if __name__=='__main__':
 if sys.argv[1]=='fetch':fetch(sys.argv[2],sys.argv[3])
 elif sys.argv[1]=='read':
  p=pathlib.Path(sys.argv[2]);d=freeze(p);print(d.decode(errors='replace')[int(sys.argv[3]):int(sys.argv[4])]);assert sha(p.read_bytes())==sha(d)
 elif sys.argv[1]=='questions':
  import re
  for name in sys.argv[2:]:
   p=L/'primary'/name;d=freeze(p);s=d.decode(errors='replace');print('\nSOURCE',name,s[:700])
   for m in re.finditer(r'(?:Conjecture|Question|Problem)\s+\d+[.\d]*',s):
    print('OFFSET',m.start(),'PAGE',s[:m.start()].count('\f')+1,s[max(0,m.start()-100):m.start()+1600])
   assert sha(p.read_bytes())==sha(d)
