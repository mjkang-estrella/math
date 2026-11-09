import pathlib,json,hashlib,datetime,urllib.request,subprocess,resource,os
O=pathlib.Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2]
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def fetch(url,name):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat();p=O/'sources'/name;p.parent.mkdir(exist_ok=True)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=30) as r: data=r.read();status=r.status
  p.write_bytes(data);h=hashlib.sha256(data).hexdigest()
 except Exception as e:status=str(e);h=None
 rec={'utc':t,'url':url,'status':status,'sha256':h,'file':str(p) if h else None};print(json.dumps(rec));
 with (O/'receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 if h and data[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],check=True,timeout=20)
if __name__=='__main__':
 import sys
 if sys.argv[1]=='fetch':fetch(sys.argv[2],sys.argv[3])
 elif sys.argv[1]=='history':
  d=json.load(open(O/'extracted.json'));pattern='|'.join(d);r=subprocess.run(['rg','-l',pattern,str(B),'--glob','*.md','--glob','*.json','--glob','!reservation.json','--glob','!mathdb*','--glob','!expanded-corpus-r45/**'],capture_output=True,text=True,timeout=60);(O/'history-paths.txt').write_text(r.stdout);print(r.stdout[:18000])
