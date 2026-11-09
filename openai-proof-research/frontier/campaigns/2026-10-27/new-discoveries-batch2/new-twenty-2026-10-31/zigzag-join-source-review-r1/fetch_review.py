import os,resource,json,hashlib,datetime,urllib.request
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
r=Path(__file__).resolve().parent;s=r/'sources';s.mkdir(exist_ok=True)
urls={'source-abs':'https://arxiv.org/abs/math/0405279','classification-abs':'https://arxiv.org/abs/math/0310165','successor-abs':'https://arxiv.org/abs/1509.03754','registry-history':'https://github.com/openai/math/commits/main','registry-contents':'https://raw.githubusercontent.com/openai/math/main/CONTENTS.md','pool-projects':'https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml'}
a=[]
for name,url in urls.items():
 d={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as f: data=f.read(4000000);d.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(s/(name+'.body')).write_bytes(data)
 except Exception as e:d['error']=str(e)
 a.append(d)
(r/'fresh-receipts.json').write_text(json.dumps(a,indent=2))
print(json.dumps(a,indent=2))
