from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,subprocess
S=Path('frontier/sources/i72_graph_probability_discovery');D=S/'primary';D.mkdir(exist_ok=True)
requests=[('mww.pdf','https://users.monash.edu/~nwormald/papers/girth.pdf'),('hy-v3.pdf','https://arxiv.org/pdf/2102.00963v3'),('hy-versions.html','https://arxiv.org/abs/2102.00963'),('mww-record.html','https://www.combinatorics.org/ojs/index.php/eljc/article/view/v11i1r66'),('hutchcroft-l2.pdf','https://arxiv.org/pdf/1904.05804v2')]
records=[]
for name,url in requests:
 r={'name':name,'url':url,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-evidence/1.0'}),timeout=40) as f:
   b=f.read(); r.update(status=f.status,final_url=f.url,headers=dict(f.headers.items()),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/name).write_bytes(b)
  if name.endswith('.pdf'):
   x=subprocess.run(['pdftotext','-layout',str(D/name),str(D/name.replace('.pdf','.txt'))],capture_output=True,text=True);r['extraction']={'code':x.returncode,'stderr':x.stderr,'command':'pdftotext -layout'}
 except Exception as e:r['error']=repr(e)
 records.append(r);(S/'primary-requests.json').write_text(json.dumps(records,indent=2)+'\n')
 print(name,r.get('status',r.get('error')))
