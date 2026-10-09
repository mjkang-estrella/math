from pathlib import Path
import json,datetime,urllib.request,hashlib,concurrent.futures,re,sys
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i30_einstein_metric_stability_novelty_r3'; O=S/'literature'; O.mkdir(exist_ok=True)
ids=['1202.2912','2102.12840','1808.03774','2008.09956','2109.02449','2408.11115','1105.4648','1312.2224']
urls=[(i+'-abs.html','https://arxiv.org/abs/'+i) for i in ids]
urls += [('MW-published.pdf','https://www.ams.org/journals/btran/2023-10-27/S2330-0000-2023-00155-8/S2330-0000-2023-00155-8.pdf'),('TW-published.pdf','https://www.ams.org/journals/jams/2015-28-04/S0894-0347-2015-00834-7/S0894-0347-2015-00834-7.pdf'),('HKRX-published.pdf','https://www.ams.org/journals/tran/2020-373-11/S0002-9947-2020-08177-X/S0002-9947-2020-08177-X.pdf')]
if len(sys.argv)>1: urls=[(sys.argv[1],sys.argv[2])]
def fetch(item):
 name,url=item; d=dict(url=url,attempted=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 I30 scholarly comparison'}),timeout=25) as r:
   b=r.read();d.update(status=r.status,final_url=r.url)
  p=O/name;p.write_bytes(b); d.update(path=str(p.relative_to(R)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if name.endswith('html'): d['versions']=sorted(set(re.findall(r'\[v(\d+)\]',b.decode(errors='replace'))),key=int)
 except Exception as e:d['error']=str(e)
 return d
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool: rows=list(pool.map(fetch,urls))
f=S/'new-primary-manifest.json'; old=json.loads(f.read_text()) if f.exists() else [];f.write_text(json.dumps(old+rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
