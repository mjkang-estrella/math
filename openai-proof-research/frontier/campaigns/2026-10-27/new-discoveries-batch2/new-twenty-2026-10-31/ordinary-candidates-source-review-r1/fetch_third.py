import requests,pathlib,json,hashlib,datetime,concurrent.futures,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
r=pathlib.Path(__file__).parent
urls={"omega-library":"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/7327fcf9a7e910c7f7bac0b2a7ed0aac9e3cc02d?recursive=1","omega-problems":"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/6829b90377cf0d5712a42527812611550884d6ba?recursive=1","brosch-citers":"https://api.openalex.org/works?filter=cites:W3164941252&per-page=100","matching-citers":"https://api.openalex.org/works?filter=cites:W3106856487&per-page=100","author-research":"https://www.math.mcgill.ca/atserunyan/research.html","thesis-brosch":"https://www.danielbrosch.com/assets/pdfs/Thesis.pdf","mo-primary-model":"https://arxiv.org/pdf/1112.4760"}

def fetch(item):
 k,u=item
 try:
  a=requests.get(u,timeout=45); (r/(k+".body")).write_bytes(a.content); o={"url":u,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"status":a.status_code,"final_url":a.url,"sha256":hashlib.sha256(a.content).hexdigest(),"bytes":len(a.content)}
 except Exception as e:o={"url":u,"error":str(e)}
 (r/(k+".receipt.json")).write_text(json.dumps(o,indent=2));return k,o
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for k,o in ex.map(fetch,urls.items()):print(k,json.dumps(o),flush=True)
