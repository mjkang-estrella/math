from pathlib import Path
import requests,hashlib,json,datetime,subprocess,concurrent.futures
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i31_nonconical_no_mcm/literature'
items={'pinkham':'https://www.numdam.org/item/AST_1974__20__1_0.pdf','coughlan-sano':'https://arxiv.org/pdf/1601.02381v3','bauer-catanese-rigid':'https://arxiv.org/pdf/1609.08128v1','bauer-catanese-equations':'https://arxiv.org/pdf/1803.02984v2','artin-notes':'https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr54.pdf','anghel-acm':'https://arxiv.org/pdf/2609.15589v1','chen-local':'https://arxiv.org/pdf/2609.24142v1','chen-sun':'https://arxiv.org/pdf/1808.02172v1'}
for name,id in [('coughlan-sano','1601.02381'),('bauer-catanese-rigid','1609.08128'),('bauer-catanese-equations','1803.02984'),('anghel-acm','2609.15589'),('chen-local','2609.24142'),('chen-sun','1808.02172')]:items[name+'-history']='https://arxiv.org/abs/'+id

def get(it):
 name,url=it; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  r=requests.get(url,timeout=55);b=r.content;pdf=b.startswith(b'%PDF');p=OUT/(name+('.pdf' if pdf else '.html'));p.write_bytes(b)
  row=dict(name=name,url=url,final_url=r.url,status=r.status_code,utc=now,path=str(p.relative_to(ROOT)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if pdf:subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);row['text_path']=str(p.with_suffix('.txt').relative_to(ROOT))
  return row
 except Exception as e:return dict(name=name,url=url,utc=now,error=str(e))
rows=list(concurrent.futures.ThreadPoolExecutor(max_workers=6).map(get,items.items()))
(OUT/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k in ('name','status','bytes','error')} for x in rows],indent=2))
