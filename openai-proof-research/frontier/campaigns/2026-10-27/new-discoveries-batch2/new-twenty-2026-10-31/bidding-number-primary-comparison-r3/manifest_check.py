import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,subprocess,sys,time
lane=pathlib.Path(__file__).resolve().parent
files=[]
for root,dirs,names in os.walk(lane,followlinks=False):
 for name in names:
  p=pathlib.Path(root)/name
  if name in ['manifest.json','manifest-verification.json']:continue
  assert not p.is_symlink()
  files.append({'path':str(p.relative_to(lane)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
def write(n,x):
 p=subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),n],input=json.dumps(x,indent=2),text=True,capture_output=True,timeout=15);assert p.returncode==0
write('manifest.json',{'files':sorted(files,key=lambda x:x['path']),'scope':'r3 lane only; manifest and its verification excluded to avoid self-reference'})
m=json.loads((lane/'manifest.json').read_text());bad=[]
for r in m['files']:
 p=(lane/r['path']).resolve();assert p.is_relative_to(lane)
 d=p.read_bytes()
 if len(d)!=r['bytes'] or hashlib.sha256(d).hexdigest()!=r['sha256']:bad.append(r['path'])
for tag in ['before','after']:
 d=json.loads((lane/('frozen-'+tag+'.json')).read_text());assert d['count']==341 and not d['mismatches']
write('manifest-verification.json',{'count':len(files),'mismatches':bad,'frozen_before':341,'frozen_after':341,'caps_before_reads':True,'self_highwater_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'children_reaped':True,'exit_at_receipt':0})
assert not bad
print(json.dumps({'artifact_count':len(files),'mismatches':bad,'frozen_before_after':[341,341]}))
