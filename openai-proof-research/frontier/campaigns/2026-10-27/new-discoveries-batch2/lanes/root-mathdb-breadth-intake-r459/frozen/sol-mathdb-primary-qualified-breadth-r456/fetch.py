from pathlib import Path
import json,urllib.request,urllib.error,datetime,hashlib
L=Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
urls=[('owr-2025-42','https://ems.press/journals/owr/articles/14299518'),('owr-2025-45','https://ems.press/journals/owr/articles/14299574'),('owr-2025-49','https://ems.press/journals/owr/articles/14299580'),('owr-2025-5','https://ems.press/journals/owr/articles/14299090'),('owr-2026-1','https://ems.press/journals/owr/articles/14299905'),('owr-2026-11','https://ems.press/journals/owr/articles/14299916'),('owr-2026-8','https://ems.press/journals/owr/articles/14299911'),('brady','https://arxiv.org/pdf/0709.0690'),('colliding','https://arxiv.org/pdf/0709.4387'),('q-catalan','https://arxiv.org/pdf/0708.2574'),('bandwidth-source','https://arxiv.org/pdf/0707.2522'),('hirsch-successor','https://arxiv.org/pdf/1006.2814')]
entries=[];blocked=set()
for name,url in urls:
 host=urllib.parse.urlparse(url).netloc
 if host in blocked:
  entries.append(dict(name=name,url=url,status='NOT_REQUESTED_HOST_STOP'));continue
 e=dict(name=name,url=url,version='publisher article id or arXiv unversioned response; see headers',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-check/1.0'}),timeout=25) as r:
   raw=r.read(16*1024*1024+1);assert len(raw)<=16*1024*1024
   ext='.pdf' if raw.startswith(b'%PDF') else '.html';p=L/'sources'/(name+ext);p.write_bytes(raw)
   hp=L/'sources'/(name+'.headers');hp.write_text(str(r.headers))
   e.update(status=r.status,file=str(p.relative_to(L)),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),resolved_url=r.url)
   if b'challenge' in raw[:10000].lower():blocked.add(host);e['status']='CHALLENGE_HOLD'
 except Exception as x:
  e.update(status='FETCH_FAILURE',error=str(x))
  if isinstance(x,urllib.error.HTTPError) and x.code in (403,429):blocked.add(host)
 entries.append(e);print(name,e['status'],flush=True)
(L/'sources.json').write_text(json.dumps(entries,indent=2)+'\n')
