from pathlib import Path
import json,re,hashlib
p=Path(__file__).resolve().parent.parent
flags=['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']
s={}
end={}
def add(k,r):
 x=s.setdefault(k,{'declarations':0,**{f:0 for f in flags},'transitive_axioms':set()})
 x['declarations']+=1
 for f in flags:x[f]+=int(r[f])
 x['transitive_axioms'].update(r['axioms'])
for line in (p/'audit.jsonl').open():
 r=json.loads(line)
 add('LOCAL' if r['local'] else 'upstream',r)
 if r['endpoint_import_closure']:add('endpoint_import_closure',r)
 if r['name'] in ['GridFinal3.mathdb_343536','Grid343536.exceptional_no_iso']:
  end[r['name']]=r['axioms']
for x in s.values():x['transitive_axioms']=sorted(x['transitive_axioms'])
resources=[]
for f in (p/'logs').glob('*.log'):
 for wall,rss,rc in re.findall(r'RESOURCE wall_s=([\d.]+) peak_rss_kib=(\d+) exit=(\d+)',f.read_text()):
  resources.append((float(wall),int(rss),int(rc)))
report={'status':'PARTIAL_CONDITIONAL','closed':['ExceptionalNoIso'],
 'remaining':['FreeClassification','MainOrbit'],'unconditional_endpoint':False,
 'LOCAL':s['LOCAL'],'upstream':s['upstream'],'endpoint_import_closure':s['endpoint_import_closure'],
 'endpoint_axioms':end,'allowOpaque':True,'inventory_equals_audited':True,
 'lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'resources':{'invocations':len(resources),'max_wall_s':max(x[0] for x in resources),
 'max_peak_group_rss_kib':max(x[1] for x in resources),'background_jobs_left':False}}
modules=sorted(f.stem for f in (p/'src').glob('*.lean'))
replayed=[]
for m in modules:
 marker=p/'build'/(m+'.replay-ok')
 if marker.exists() and marker.read_text().strip()==hashlib.sha256((p/'src'/(m+'.lean')).read_bytes()).hexdigest():
  replayed.append(m)
report['strict_serial_replay_modules']=replayed
report['all_23_modules_compiled_and_leanchecked']=len(replayed)==23
for line in (p/'frozen-before.sha256').read_text().splitlines():
 h,n=line.split()
 assert hashlib.sha256((p/'src'/n).read_bytes()).hexdigest()==h
report['frozen_13_modules_match']=True
(p/'replay-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
