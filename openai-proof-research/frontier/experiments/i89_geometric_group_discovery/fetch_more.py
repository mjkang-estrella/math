from pathlib import Path
import urllib.request,datetime,json,hashlib,subprocess
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i89_geometric_group_discovery/primary'; log=S/'responses-more.jsonl'
if log.exists():raise SystemExit('refusing overwrite')
urls=[('lcm','https://arxiv.org/pdf/0907.3681'),('lcm-version','https://arxiv.org/abs/0907.3681'),('vcs-growth','https://arxiv.org/pdf/1402.6974'),('vcs-growth-version','https://arxiv.org/abs/1402.6974'),('ikn-version','https://arxiv.org/abs/1210.5829')]
for name,url in urls:
 d={'name':name,'url':url,'captured':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=45) as r:b=r.read();d.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  p=S/(name+('.pdf' if b.startswith(b'%PDF') else '.html'));p.write_bytes(b);d.update(local=p.relative_to(R).as_posix(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF'):
   out=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True).stdout;q=S/(name+'.txt');q.write_bytes(out);d.update(text=q.relative_to(R).as_posix(),text_sha256=hashlib.sha256(out).hexdigest())
 except Exception as e:d['error']=str(e)
 with log.open('a') as f:f.write(json.dumps(d,sort_keys=True)+'\n')
 print(name,d.get('status'),d.get('error',''),flush=True)
