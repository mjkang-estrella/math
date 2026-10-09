from pathlib import Path
import urllib.request, hashlib,json,datetime,re,concurrent.futures,subprocess
ROOT=Path(__file__).resolve().parents[3]; OUT=ROOT/'frontier/sources/i27_geometric_analysis_discovery/literature';OUT.mkdir(parents=True,exist_ok=True)
IDS=['1505.03428','2408.11115','2102.12840','2410.08667','2606.01511','2401.00279','2509.21508','2609.20647','2503.00649','2609.19979']
def fetch(url,path):
 req=urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'})
 with urllib.request.urlopen(req,timeout=45) as r:b=r.read();final=r.url;typ=r.headers.get('Content-Type')
 path.write_bytes(b)
 return {'url':url,'final_url':final,'path':str(path.relative_to(ROOT)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'content_type':typ}
def run(i):
 rows=[]
 try:
  p=OUT/(i+'.abs.html');rows.append(fetch('https://arxiv.org/abs/'+i,p));s=p.read_text();vs=re.findall(re.escape(i)+r'v(\d+)',s);v=max(map(int,vs));version=i+'v'+str(v)
  p=OUT/(version+'.pdf');rows.append(fetch('https://arxiv.org/pdf/'+version,p));assert p.read_bytes().startswith(b'%PDF');subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  rows[-1]['version']=version
 except Exception as e:rows.append({'id':i,'error':str(e)})
 return rows
rows=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:
 for batch in ex.map(run,IDS):rows+=batch
(OUT/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{'url':r.get('url'),'version':r.get('version'),'bytes':r.get('bytes'),'error':r.get('error')} for r in rows],indent=2))
