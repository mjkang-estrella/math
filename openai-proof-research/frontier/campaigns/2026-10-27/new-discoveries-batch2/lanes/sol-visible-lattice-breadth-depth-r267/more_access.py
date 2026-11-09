from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime
L=Path(__file__).parent
urls=[('arxiv-general','https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':'all:"visible lattice" AND (all:parallelogram OR all:polygon)','max_results':10})),('published-chapter','https://link.springer.com/chapter/10.1007/978-3-030-67996-5_19')]
for name,url in urls:
 r={'label':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-check/1.0'}),timeout=20) as f:raw=f.read(2000000);r['status']=f.status
  r.update(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest());(L/(name+'.body')).write_bytes(raw)
 except Exception as e:r['failure']=str(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r))
