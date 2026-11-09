import urllib.request,pathlib,json,hashlib,time,sys
L=pathlib.Path(__file__).parent;D=L/'sources';D.mkdir(exist_ok=True)
out=[]
for name,url in [tuple(x.split('|',1)) for x in sys.argv[1:]]:
 p=D/name
 if p.exists():print('immutable exists',name);continue
 r={'url':url,'time':time.time(),'name':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical research contact-free retrieval'}),timeout=25) as f:
   data=f.read(16000000);r['status']=f.status
  p.write_bytes(data);h=hashlib.sha256(data).hexdigest();r['sha256']=h
  q=L/'frozen'/name;q.write_bytes(data)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
  r['frozen']=str(q);print(name,len(data),h)
 except Exception as e:r['error']=str(e);print(name,str(e))
 out.append(r)
 with (L/'source-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
