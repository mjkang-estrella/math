import requests,hashlib,json,datetime,pathlib,concurrent.futures
P=pathlib.Path(__file__).resolve().parents[1]
urls={
'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD',
'omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
'later':'https://arxiv.org/html/2507.14568v3',
'zhou':'https://match.pmf.kg.ac.rs/electronic_versions/Match52/match52_113-118.pdf',
'nikiforov':'https://arxiv.org/pdf/1308.3867',
'citing':'https://api.openalex.org/works/https://doi.org/10.48550/arXiv.2411.04881',
}
def get(kv):
 k,u=kv;t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  r=requests.get(u,timeout=35);b=r.content;(P/'sources'/k).write_bytes(b)
  d=dict(url=u,final_url=r.url,status=r.status_code,utc=t,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:d=dict(url=u,utc=t,error=str(e))
 (P/'receipts'/f'{k}.json').write_text(json.dumps(d,indent=2));return d
if __name__=='__main__':
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:
  for r in e.map(get,urls.items()):print(json.dumps(r),flush=True)
