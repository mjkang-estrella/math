import requests,json,hashlib,datetime,pathlib,resource
resource.setrlimit(resource.RLIMIT_CPU,(60,60)); resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
p=pathlib.Path('sources');p.mkdir(exist_ok=True)
urls={
'openai-head':'https://api.github.com/repos/OpenAI/math/commits/HEAD',
'omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
'source-current':'https://arxiv.org/abs/2408.01288',
'anticode-search':'https://arxiv.org/search/?query=%22anticodes%22+%22diameter%22&searchtype=all&abstracts=show&order=-announced_date_first&size=50',
'rigid-search':'https://arxiv.org/search/?query=%22rigid%22+%22hypercube%22&searchtype=all&abstracts=show&order=-announced_date_first&size=50',
'facet-search':'https://arxiv.org/search/?query=%22Facets+in+the+Vietoris%22&searchtype=all&abstracts=show&order=-announced_date_first&size=50',
'predecessor-feng':'https://arxiv.org/html/2305.07084',
'predecessor-shukla':'https://arxiv.org/html/2202.02756',
}
for name,url in urls.items():
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,timeout=35); data=r.content; (p/(name+'.body')).write_bytes(data); rec.update(status=r.status_code,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:rec['error']=str(e)
 (p/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
