from pathlib import Path
import resource,os,json,hashlib,datetime,concurrent.futures,urllib.request,re,subprocess
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).resolve().parents[1];s=p/'sources';jobs=[];inventory={}
for f in s.glob('*.abs.html'):
 a=f.name[:-9].replace('math_','math/'); text=f.read_text();versions=sorted(set(re.findall(re.escape(a)+r'v(\d+)',text)),key=int); versions=versions or ['1']; inventory[a]={'versions':versions,'doi':re.findall(r'https://doi.org/([^"<> ]+)',text)}
 for v in versions:jobs.append((a,v))
(s/'version-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
def fetch(job):
 a,v=job;url='https://arxiv.org/pdf/'+a+'v'+v;f=s/(a.replace('/','_')+'v'+v+'.pdf');rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=18) as h:data=h.read(15000000);rec.update(status=h.status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));f.write_bytes(data)
  if data[:4]==b'%PDF':
   q=subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],capture_output=True,text=True,timeout=12);rec['pdftotext_exit']=q.returncode
 except Exception as e:rec['error']=str(e)
 f.with_suffix('.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
 for r in ex.map(fetch,jobs):print(json.dumps(r),flush=True)
