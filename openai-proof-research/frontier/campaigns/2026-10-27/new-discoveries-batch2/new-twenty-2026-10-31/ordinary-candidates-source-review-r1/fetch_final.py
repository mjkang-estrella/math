import requests,pathlib,json,hashlib,datetime,concurrent.futures,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
r=pathlib.Path(__file__).parent
urls={"bipartite-matching-prior":"https://arxiv.org/pdf/1807.06556","omega-leaf-body":"https://raw.githubusercontent.com/the-omega-institute/trureturing/88f355e538076c5d1665984f232df4015fb25e58/D5/S3/Combinatorics/Graph/RedundantLeafMatching.lean","openai-matching-body":"https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/build/main.tex"}

def fetch(item):
 k,u=item
 try:
  a=requests.get(u,timeout=45); (r/(k+".body")).write_bytes(a.content); o={"url":u,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"status":a.status_code,"final_url":a.url,"sha256":hashlib.sha256(a.content).hexdigest(),"bytes":len(a.content)}
 except Exception as e:o={"url":u,"error":str(e)}
 (r/(k+".receipt.json")).write_text(json.dumps(o,indent=2));return k,o
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for k,o in ex.map(fetch,urls.items()):print(k,json.dumps(o),flush=True)
