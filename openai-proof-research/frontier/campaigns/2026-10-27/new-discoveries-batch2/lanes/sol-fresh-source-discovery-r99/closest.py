exec(open(__file__.replace('closest.py','fetch.py')).read().split('urls=')[0])
urls={'super-successor.pdf':'https://www.utupub.fi/bitstream/handle/10024/188196/1-s2.0-S0166218X24000532-main.pdf?isAllowed=y&sequence=1','super-complexity.pdf':'https://users.fmf.uni-lj.si/klavzar/preprints/1-s2.0-S0304397523004504-main.pdf','finite-original.html':'https://arxiv.org/html/2305.05632v3','finite-original-abs.html':'https://arxiv.org/abs/2305.05632','finite-successor-abs.html':'https://arxiv.org/abs/2505.24072'}
log=[]
for n,u in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research-source-audit'}),timeout=25) as r:b=r.read();s=r.status
  f='sources/'+n;(P/f).write_bytes(b);log.append(dict(url=u,status=s,file=f,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));print(n,len(b))
 except Exception as e:log.append(dict(url=u,error=str(e)));print(n,e)
(P/'http-closest.json').write_text(json.dumps(log,indent=2))
