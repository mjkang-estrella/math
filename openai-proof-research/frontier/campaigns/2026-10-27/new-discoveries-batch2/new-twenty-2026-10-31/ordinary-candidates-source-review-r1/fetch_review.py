import requests,pathlib,json,hashlib,datetime,concurrent.futures,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
r=pathlib.Path(__file__).parent
urls={"openai-live":"https://api.github.com/repos/openai/math/commits/HEAD","omega-live":"https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD","arxiv-matching":"https://arxiv.org/abs/2011.11187","journal-matching":"https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-66/issue-1/Characterization-of-saturated-graphs-related-to-pairs-of-disjoint-matchings/10.1215/00192082-9719963.full","author-matching":"https://www.math.mcgill.ca/atserunyan/Research.html","queue-citer":"https://arxiv.org/pdf/2111.05777"}
urls.update({f"matching-v{i}":f"https://arxiv.org/pdf/2011.11187v{i}" for i in range(2,6)})
def fetch(item):
 k,u=item
 try:
  a=requests.get(u,timeout=45); (r/(k+".body")).write_bytes(a.content); o={"url":u,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"status":a.status_code,"final_url":a.url,"sha256":hashlib.sha256(a.content).hexdigest(),"bytes":len(a.content)}
 except Exception as e:o={"url":u,"error":str(e)}
 (r/(k+".receipt.json")).write_text(json.dumps(o,indent=2));return k,o
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for k,o in ex.map(fetch,urls.items()):print(k,json.dumps(o),flush=True)
