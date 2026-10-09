from pathlib import Path
import requests,hashlib,json,datetime,subprocess,concurrent.futures
out=Path('frontier/sources/i28_algebra_discovery/literature')
items=[('bot-v1','https://arxiv.org/pdf/1010.0565v1'),('knus-sridharan','https://people.math.ethz.ch/~knus/sridharan/merkurjev84.pdf')]+[(i+'-abs','https://arxiv.org/abs/'+a) for i,a in [('bot','1010.0565'),('anghel-acm','2609.15589'),('anghel-ulrich','2609.02718'),('chen-local','2609.24142'),('chen-sun','1808.02172'),('loring','1302.0349'),('bhm','2410.18372'),('quasi-gorenstein','2608.10962')]]
def one(item):
 name,url=item;r=requests.get(url,timeout=50);b=r.content;pdf=b.startswith(b'%PDF');p=out/(name+('.pdf' if pdf else '.html'));p.write_bytes(b)
 row=dict(name=name,url=url,final_url=r.url,status=r.status_code,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),pdf=pdf)
 if pdf:subprocess.run(['pdftotext','-layout',str(p),str(out/(name+'.txt'))],check=True)
 else:
  from bs4 import BeautifulSoup
  (out/(name+'.txt')).write_text(BeautifulSoup(b,'html.parser').get_text('\n'))
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:rows=list(ex.map(one,items))
(out/'additional-manifest.json').write_text(json.dumps(rows,indent=2)+'\n');print([(r['name'],r['status'],r['bytes']) for r in rows])
