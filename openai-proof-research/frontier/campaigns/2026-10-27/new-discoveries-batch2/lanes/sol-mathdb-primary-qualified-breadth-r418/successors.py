from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,re,subprocess
R=Path(__file__).resolve().parent;P=R/'primary';log=[]
queries=['mapping class group three involutions','pseudo-Anosov non ergodic SU(2) character variety','profinite rigidity free groups']
for i,q in enumerate(queries):
 url='https://arxiv.org/search/?'+urllib.parse.urlencode({'query':q,'searchtype':'all','abstracts':'show','order':'-announced_date_first','size':'25'})
 e={'query':q,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:data=f.read(1500000);e.update(status=f.status,final_url=f.url)
  p=P/('search-'+str(i)+'.html');p.write_bytes(data);e.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),size=len(data))
  log.append(e);(R/'successor-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
  from bs4 import BeautifulSoup
  soup=BeautifulSoup(data,'html.parser');results=soup.select('li.arxiv-result');print(q)
  for x in results[:8]: print(x.get_text(' ',strip=True)[:1100])
 except Exception as ex:e['failure']=str(ex);log.append(e) if e not in log else None;print(q,str(ex))
 (R/'successor-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
