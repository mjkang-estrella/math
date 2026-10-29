from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
p=Path(__file__).resolve().parent;s=p/'live';s.mkdir(exist_ok=True);rows=[]
for name,url in [('arxiv-abs.html','https://arxiv.org/abs/2507.13566'),('mtu.html','https://digitalcommons.mtu.edu/michigantech-p2/2399/'),('journal-preview.html','https://www.researchgate.net/publication/399831893_Combinatorial_proof_of_a_congruence_for_partitions_into_two_sizes_of_part'),('omega.html','https://github.com/the-omega-institute/trureturing'),('openai.html','https://github.com/adamczewski/GPT6-Astra')]:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'live/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=20) as f:data=f.read();r.update(status=f.status,final_url=f.url)
 except urllib.error.HTTPError as e:data=e.read();r.update(status=e.code,final_url=e.url)
 except Exception as e:r['error']=str(e);rows.append(r);continue
 (s/name).write_bytes(data);r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));rows.append(r)
(p/'live-http.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
