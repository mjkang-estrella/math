from pathlib import Path
import urllib.request,json,hashlib,subprocess,datetime,concurrent.futures
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i154_dimension_independent_oracle_tolerance/primary';S.mkdir(exist_ok=True)
items=[('shifted1','2311.14520',True),('shifted3','2412.17997',True),('inexact','1710.00095',True),('picard-current','2609.06906',False),('chen-liu-current','2610.06724',False),('hhp-current','1708.02216',False)]
def fetch(it):
 name,num,pdf=it;out=[]
 for ext,url in [('html','https://arxiv.org/abs/'+num)]+([('pdf','https://arxiv.org/pdf/'+num)] if pdf else []):
  row={'url':url,'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=30) as f:b=f.read();row.update(status=f.status,final_url=f.url)
   p=S/(name+'.'+ext);p.write_bytes(b);row.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
   if ext=='pdf':
    dest=p.with_suffix('.txt');z=subprocess.run(['pdftotext','-layout',str(p),str(dest)],capture_output=True,text=True);row['extraction']={'exit':z.returncode,'stderr':z.stderr}
    if z.returncode==0:row.update(text_path=str(dest.relative_to(R)),text_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),splitlines=len(dest.read_text().splitlines()))
  except Exception as e:row['error']=repr(e)
  out.append(row)
 return out
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as p: rows=[y for x in p.map(fetch,items) for y in x]
(S/'retrieval.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
