import urllib.request,pathlib,json,datetime,hashlib
P=pathlib.Path(__file__).parent; out=[]
for a in ['0910.5490v1','1001.2942v1','0910.3831v1']:
 u='https://arxiv.org/html/'+a; row={'url':u,'version':a,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as r:b=r.read();row['final_url']=r.url
  (P/(a+'.html')).write_bytes(b);row.update(path=a+'.html',size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:row['failure']=str(e)
 out.append(row)
(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
