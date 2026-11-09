import pathlib,json,hashlib,datetime,urllib.request,concurrent.futures,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
def fetch(t):
 name,url=t;p=D/'sources'/name
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':str(p)}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research source inspection'}),timeout=18) as f: b=f.read();r['status']=f.status
  p.write_bytes(b);r['sha256']=hashlib.sha256(b).hexdigest();r['bytes']=len(b)
  if name.endswith('.pdf') and b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=15)
 except Exception as e:r['error']=str(e)
 return r
if __name__=='__main__':
 import sys
 o=json.loads((D/'extracted.json').read_text());tasks=[]
 if 'registry' in sys.argv:
  tasks=[(n+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD') for n,repo in [('openai','openai/math'),('omega','the-omega-institute/trureturing')]]
 else:
  seen=set()
  for i,v in o.items():
   a=v['source_url'].split('/abs/')[-1]
   if a not in seen:tasks.append((a+'.pdf','https://arxiv.org/pdf/'+a));seen.add(a)
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:out=list(ex.map(fetch,tasks))
 (D/'outputs'/('registry-receipts.json' if 'registry' in sys.argv else 'source-receipts.json')).write_text(json.dumps(out,indent=2)+'\n')
 for r in out: print(r)
