import requests,pathlib,json,hashlib,datetime,concurrent.futures,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
r=pathlib.Path(__file__).parent
urls={"nsf-matching":"https://par.nsf.gov/servlets/purl/10358584","omega-root":"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/0a9291caee29a54bf7f0a7d0de44a2b240a6eb12","matching-citations":"https://api.openalex.org/works/https://doi.org/10.1215/00192082-9719963","brosch-citations":"https://api.openalex.org/works/https://doi.org/10.1137/20M1369592","mo-classical":"https://projecteuclid.org/journals/journal-of-the-american-statistical-association/volume-62/issue-317/A-Multivariate-Exponential-Distribution/10.1080/01621459.1967.10482885.full","author-page":"https://www.math.mcgill.ca/atserunyan/"}

def fetch(item):
 k,u=item
 try:
  a=requests.get(u,timeout=45); (r/(k+".body")).write_bytes(a.content); o={"url":u,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"status":a.status_code,"final_url":a.url,"sha256":hashlib.sha256(a.content).hexdigest(),"bytes":len(a.content)}
 except Exception as e:o={"url":u,"error":str(e)}
 (r/(k+".receipt.json")).write_text(json.dumps(o,indent=2));return k,o
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for k,o in ex.map(fetch,urls.items()):print(k,json.dumps(o),flush=True)
