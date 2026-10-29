exec(open(__file__.replace('final_delta.py','fetch.py')).read().split('urls=')[0])
a=json.loads((P/'sources/omega-head.json').read_text())['sha'];h=json.loads((P/'sources/omega-head-final.json').read_text())['sha'];log=[]
u='https://api.github.com/repos/the-omega-institute/trureturing/compare/'+a+'...'+h
try:
 with urllib.request.urlopen(u,timeout=25) as r:b=r.read()
 (P/'sources/omega-final-delta.json').write_bytes(b);d=json.loads(b);log.append(dict(url=u,file='sources/omega-final-delta.json',status=200,sha256=hashlib.sha256(b).hexdigest()));print(d.get('total_commits'),len(d.get('files',[])))
 for i,x in enumerate(d.get('files',[])):
  if x['status']=='removed':continue
  u='https://raw.githubusercontent.com/the-omega-institute/trureturing/'+h+'/'+urllib.parse.quote(x['filename'])
  try:
   with urllib.request.urlopen(u,timeout=25) as r:b=r.read()
   f='sources/omega-final-body-'+str(i)+'.txt';(P/f).write_bytes(b);log.append(dict(url=u,status=200,file=f,sha256=hashlib.sha256(b).hexdigest()));print(x['filename'],len(b))
  except Exception as e:log.append(dict(url=u,error=str(e)))
except Exception as e:log.append(dict(url=u,error=str(e)))
(P/'http-final-delta.json').write_text(json.dumps(log,indent=2))
