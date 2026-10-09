from pathlib import Path
import requests,hashlib,json,datetime,subprocess,concurrent.futures
out=Path('frontier/sources/i28_algebra_discovery/literature');out.mkdir(exist_ok=True)
items=[('anghel-ulrich','https://arxiv.org/pdf/2609.02718v1'),('anghel-acm','https://arxiv.org/pdf/2609.15589v1'),('chen-local','https://arxiv.org/pdf/2609.24142v1'),('chen-sun','https://arxiv.org/pdf/1808.02172v1'),('bot','https://arxiv.org/pdf/1010.0565v2'),('loring','https://arxiv.org/pdf/1302.0349v3'),('bhm','https://arxiv.org/pdf/2410.18372v2'),('milne-cft','https://www.jmilne.org/math/CourseNotes/CFT.pdf'),('quasi-gorenstein','https://arxiv.org/pdf/2608.10962v1')]
def one(item):
 name,url=item; r=requests.get(url,timeout=50); b=r.content;pdf=b.startswith(b'%PDF');p=out/(name+('.pdf' if pdf else '.response'));p.write_bytes(b)
 row=dict(name=name,url=url,final_url=r.url,status=r.status_code,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),pdf=pdf)
 if pdf:
  t=out/(name+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);row['text_path']=str(t)
 return row
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:rows=list(ex.map(one,items))
(out/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:x[k] for k in ['name','status','bytes','pdf']} for x in rows],indent=2))
