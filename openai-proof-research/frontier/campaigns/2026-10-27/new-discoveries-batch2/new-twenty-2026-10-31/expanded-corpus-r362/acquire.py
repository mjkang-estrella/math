exec(compile((__import__('pathlib').Path(__file__).resolve().parent/'research.py').read_text(), 'research.py','exec'))
from concurrent.futures import ThreadPoolExecutor

def fetch(item):
 name,url=item; t=time.monotonic(); rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),method='GET')
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematics source review (public read only)'}),timeout=22) as f:
   b=f.read(12*1024*1024+1);assert len(b)<=12*1024*1024
   rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b));put('sources/'+name,b)
 except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
 rec['wall_seconds']=time.monotonic()-t;js('http/'+name+'.json',rec);print(name,rec.get('status'),rec.get('error',''),rec.get('bytes'))
 return rec
if sys.argv[1]=='fetch':
 batch=json.loads((L/sys.argv[2]).read_text())
 with ThreadPoolExecutor(max_workers=2) as ex:out=list(ex.map(fetch,batch))
 receipt('acquire-'+sys.argv[2].replace('.json',''),dict(fetches=out,threads_joined=True))
elif sys.argv[1]=='prepare':
 js('batch1.json',[(str(v['mathdb_id'])+'.pdf',v['source_url'].replace('/abs/','/pdf/')) for v in r['rows']])
 # Only exact allowlist paths; suppress protected names before any opens. Only matching keyed entries retained.
 allowed=json.loads((L/'historical-results-allowlist.json').read_text());hits=[];scanned=0
 needles=[str(x) for x in r['ids']]+[v['source_url'].split('/')[-1] for v in r['rows']]
 for s in allowed:
  if any(x in s.lower() for x in ['crown','lower-support','fullside','primality']):continue
  p=pathlib.Path(s)
  if not p.is_file():continue
  raw=p.read_bytes();scanned+=1
  if not any(n.encode() in raw for n in needles):continue
  obj=json.loads(raw)
  def walk(o,path=''):
   if isinstance(o,dict):
    if any(str(o.get(k,'')) in set(map(str,r['ids'])) for k in ['mathdb_id','id']):hits.append(dict(path=s,key=path,entry=o));return
    for k,v in o.items():
     if k in set(map(str,r['ids'])):hits.append(dict(path=s,key=path+'/'+k,entry=v))
     elif isinstance(v,(list,dict)):walk(v,path+'/'+k)
   elif isinstance(o,list):
    for i,v in enumerate(o):walk(v,path+'/'+str(i))
  walk(obj)
 js('history-keyed.json',dict(exact_allowlist_files_processed=scanned,hits=hits,limitation='ID-keyed extraction; family textual matches not automatically excluded'))
 print('HISTORY',scanned,len(hits)); print(json.dumps(hits)[:20000])
 # Shared files: extract strict scalar keys/lines, no shared bodies printed or copied.
 for p in [L.parent/'ledger.json',L.parent/'STATUS.md',L.parents[1]/'ledger.json']:
  if not p.exists():continue
  if p.suffix=='.json':
   obj=json.loads(p.read_text()); scal={k:v for k,v in obj.items() if isinstance(v,(int,float,bool,type(None))) or (isinstance(v,str) and k in ['status','target','accepted_count','current_count'])};print(str(p),scal)
  else:
   import re
   print(str(p),re.findall(r'(?<!\d)52\s*/\s*60(?!\d)',p.read_text())[:1])
 receipt('prepare',dict(history_files=scanned))
elif sys.argv[1]=='text':
 inv=[]
 for row in r['rows']:
  k=str(row['mathdb_id']);p=L/'sources'/ (k+'.pdf')
  if not p.exists():continue
  dest=L/'sources'/(k+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(dest)],timeout=12,check=True)
  text=dest.read_text();inv.append(dict(id=k,characters=len(text),sha256=sha(dest.read_bytes()),depth='acquired and converted; excerpts separately read'))
 js('source-inventory-acquired.json',inv);receipt('text',dict(converted=len(inv),all_subprocesses_reaped=True))
