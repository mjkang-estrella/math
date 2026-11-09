import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import json,pathlib,re,hashlib,subprocess,sys,time
lane=pathlib.Path(__file__).resolve().parent
p=(lane/'../expanded-corpus-r361/results.json').resolve();allow=json.loads((lane/'historical-results-allowlist.json').read_text());assert str(p) in allow
b=p.read_bytes();j=json.loads(b)
def walk(x):
 if isinstance(x,dict):
  if str(x.get('mathdb_id',x.get('id',''))) =='355433':print(json.dumps(x,indent=2));return
  for k,v in x.items():
   if k=='355433':print(json.dumps(v,indent=2))
   elif isinstance(v,(dict,list)):walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(j)
for name in ['openai','leanpool']:
 s=(lane/('sources/'+name+'.html')).read_text();print(name,re.findall(r'"currentOid":"([a-f0-9]+)"',s)[:3])
rec={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'selection':'355433 only','utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'caps_before_reads':True,'self_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),'history-receipt.json'],input=json.dumps(rec,indent=2)+'\n',text=True,check=True,stdout=subprocess.DEVNULL)
