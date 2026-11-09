import requests,pathlib,json,hashlib,datetime,concurrent.futures,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
r=pathlib.Path(__file__).parent
urls={"polak-published":"https://ir.cwi.nl/pub/31516/31516.pdf","predecessor-published":"https://msp.org/involve/2023/16-2/involve-v16-n2-p04-s.pdf","mo-zolotarev":"https://www.mdpi.com/2227-7390/9/15/1728/pdf","omega-leaf-current":"https://raw.githubusercontent.com/the-omega-institute/trureturing/88f355e538076c5d1665984f232df4015fb25e58/D5/RedundantLeafMatching.lean"}

def fetch(item):
 k,u=item
 try:
  a=requests.get(u,timeout=45); (r/(k+".body")).write_bytes(a.content); o={"url":u,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"status":a.status_code,"final_url":a.url,"sha256":hashlib.sha256(a.content).hexdigest(),"bytes":len(a.content)}
 except Exception as e:o={"url":u,"error":str(e)}
 (r/(k+".receipt.json")).write_text(json.dumps(o,indent=2));return k,o
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for k,o in ex.map(fetch,urls.items()):print(k,json.dumps(o),flush=True)
