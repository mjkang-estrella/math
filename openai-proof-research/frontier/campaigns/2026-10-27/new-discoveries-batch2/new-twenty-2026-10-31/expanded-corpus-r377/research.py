import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,subprocess,time,datetime,sys
L=pathlib.Path(__file__).resolve().parent
receipts=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def read(p):
 t=now();b=pathlib.Path(p).read_bytes();receipts.append({'kind':'read','path':str(p),'utc':t,'bytes':len(b),'sha256':sha(b),'depth':'full bytes; semantic depth separately recorded','pid':os.getpid(),'rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss});return b
def write(name,obj):
 data=obj if isinstance(obj,str) else json.dumps(obj,ensure_ascii=False,indent=2)+'\n'
 t=now();p=subprocess.Popen([sys.executable,'-I','-B',str(L/'write_lane.py'),name],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 p.stdin.write(data.encode());p.stdin.close();samples=[]
 while p.poll() is None:
  try:
   s=pathlib.Path(f'/proc/{p.pid}/status').read_text();rss=int(s.split('VmRSS:')[1].split()[0]) if 'VmRSS:' in s else 0;samples.append(rss)
   if rss>6*1024**2:os.killpg(p.pid,9)
  except FileNotFoundError:pass
  time.sleep(.005)
 out=p.stdout.read();err=p.stderr.read();rc=p.wait();receipts.append({'kind':'writer','name':name,'utc':t,'pid':p.pid,'true_exit':rc,'sampled_rss_kib':samples,'reaped':True,'group':'no descendants spawned by writer','stderr':err.decode()});assert rc==0

def main():
 r=read(L/'reservation.json');assert sha(r)=='e138b8029732f05bf820788c9716326f6615aa60972502371e3663229c7281aa';assert read(L/'reservation.sha256').decode().strip()==sha(r)
 res=json.loads(r);ids=set(res['ids']);found={}
 corpus=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
 for p in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
  b=read(p);ch=sha(b)
  for n,line in enumerate(b.splitlines(keepends=True),1):
   # JSON parsing only for corpus record selection; no mathematical search.
   j=json.loads(line);i=j.get('mathdb_id',j.get('id'))
   try:i=int(i)
   except (ValueError,TypeError):continue
   if i in ids:
    assert i not in found
    statement=j.get('statement',j.get('statement_text',j.get('body','')))
    found[i]={'chunk_path':str(p),'chunk_sha256':ch,'line':n,'raw':line.decode(),'raw_sha256':sha(line),'parsed':j,'statement_field_used':'statement' if 'statement'in j else 'statement_text' if 'statement_text'in j else 'body','statement_sha256':sha(statement.encode()) if isinstance(statement,str) else None}
 assert set(found)==ids,(len(found),list(ids-set(found)))
 write('raw-provenance.json',found)
 a=json.loads(read(L/'historical-results-allowlist.json'));write('allowlist-inventory.json',a)
 write('extraction-receipts.json',receipts)
 print(json.dumps({'ids':res['ids'],'allowlist':a},ensure_ascii=False))
 for i in res['ids']: print('RECORD',i,json.dumps(found[i]['parsed'],ensure_ascii=False))
 print('EXIT',json.dumps({'utc':now(),'pid':os.getpid(),'exit':0,'rusage':list(resource.getrusage(resource.RUSAGE_SELF)),'cpus':sorted(os.sched_getaffinity(0))}))
if __name__=='__main__':main()
