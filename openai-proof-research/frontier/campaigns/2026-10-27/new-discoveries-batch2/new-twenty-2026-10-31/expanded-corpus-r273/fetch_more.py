import requests,json,hashlib,datetime,resource,concurrent.futures,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;s=p/'sources';r=json.loads((p/'reservation.json').read_text());inv=json.loads((p/'version-inventory.json').read_text());jobs=[]
for row in r['rows']:
 id=str(row['mathdb_id']);vv=inv.get(id,{}).get('versions',[])
 for v in vv[:-1]:jobs.append((id+'v'+v,row['source_url'].replace('/abs/','/pdf/')+'v'+v,True))
extras={'pankov':'https://arxiv.org/pdf/1509.03754','shortlinks':'https://arxiv.org/pdf/math/0310165','author-publications':'https://mathieudutsik.github.io/Publications/index.html','registry-contents':'https://raw.githubusercontent.com/openai/math/main/CONTENTS.md','registry-head':'https://github.com/openai/math/commits/main/','leanpool':'https://raw.githubusercontent.com/leanprover-community/leanprover-community.github.io/master/data/projects.yml','journal-engel':'https://ems.press/content/serial-article-files/29624','author-deza':'https://micheldeza.altervista.org/lpubHyperlink.html'}
for k,u in extras.items():jobs.append((k,u,k in ['pankov','shortlinks','journal-engel']))
def job(j):
 name,url,pdf=j;receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  a=requests.get(url,timeout=12);b=a.content;receipt.update(status=a.status_code,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),final_url=a.url);f=s/(name+('.pdf' if pdf else '.html'));f.write_bytes(b)
  if pdf and a.status_code==200 and b.startswith(b'%PDF'):receipt['text_rc']=subprocess.run(['pdftotext','-layout',str(f),str(s/(name+'.txt'))],capture_output=True,timeout=15).returncode
 except Exception as e:receipt['error']=str(e)
 (s/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2));return name,receipt
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for a in pool.map(job,jobs):print(json.dumps(a),flush=True)
