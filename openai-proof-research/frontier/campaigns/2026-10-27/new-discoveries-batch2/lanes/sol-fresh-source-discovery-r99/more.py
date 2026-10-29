exec(open(__file__.replace('more.py','fetch.py')).read().split('urls=')[0])
urls={'super-vor.pdf':'https://repositori.urv.cat/fourrepo/rest/audit/digitalobjects/DS?datastreamId=DocumentPrincipal&label=On+the+super+domination+number+of+graphs&lang=ca&mime=application%2Fpdf&objectId=imarina%3A9138942','coalition.html':'https://arxiv.org/html/2607.22686v1','finite.html':'https://arxiv.org/html/2505.24072v1','finite-abs.html':'https://arxiv.org/abs/2505.24072'}
log=json.loads((P/'http.json').read_text())
for n,u in urls.items():
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research-source-audit'}),timeout=25) as r:b=r.read();s=r.status
  f='sources/'+n;(P/f).write_bytes(b);log.append(dict(url=u,status=s,file=f,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));print(n,len(b))
 except Exception as e:log.append(dict(url=u,error=str(e)));print(n,e)
(P/'http-more.json').write_text(json.dumps(log,indent=2))
