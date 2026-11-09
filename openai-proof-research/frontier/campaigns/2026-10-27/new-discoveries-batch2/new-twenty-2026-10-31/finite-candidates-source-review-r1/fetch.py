import os,resource,requests,pathlib,hashlib,json,datetime,subprocess
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
b=pathlib.Path(__file__).parent
urls={"registry":"https://api.github.com/repos/openai/math/commits/HEAD","albert":"https://www.cs.otago.ac.nz/research/theory/Talks/CandyNim.pdf","leung-successor":"https://arxiv.org/pdf/1810.08781","furedi-index":"https://www.renyi.hu/~furedi/","boros":"https://www.renyi.hu/~furedi/publ/BorosFurediKahn_1989_MaximalIntersecting.pdf","program-tree":"https://api.github.com/repos/nmani2/candynim/git/trees/HEAD?recursive=1","goddard":"https://people.computing.clemson.edu/~goddard/papers/idomTriangleFree.pdf"}
records=[]
for name,url in urls.items():
 d={"name":name,"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,timeout=25);d.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(r.content).hexdigest()); ext="pdf" if r.content.startswith(b"%PDF") else "txt";p=b/(name+"."+ext);p.write_bytes(r.content)
  if ext=="pdf": subprocess.run(["pdftotext","-layout",str(p),str(b/(name+".txt"))],check=True,timeout=15)
 except Exception as e: d["error"]=str(e)
 records.append(d);print(d,flush=True)
(b/"access.json").write_text(json.dumps(records,indent=2))
