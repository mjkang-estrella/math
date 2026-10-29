exec(open(__file__.replace('finish_sources.py','fetch.py')).read().split('urls=')[0])
urls={'super-successor-v3.pdf':'https://arxiv.org/pdf/2209.01795v3','super-successor-abs.html':'https://arxiv.org/abs/2209.01795','omega-head-final.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head-final.json':'https://api.github.com/repos/openai/math/commits/HEAD'}
log=[]
for n,u in urls.items():
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read();s=r.status
  f='sources/'+n;(P/f).write_bytes(b);log.append(dict(url=u,status=s,file=f,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));print(n,len(b))
 except Exception as e:log.append(dict(url=u,error=str(e)))
(P/'http-final.json').write_text(json.dumps(log,indent=2))
