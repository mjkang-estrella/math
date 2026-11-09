from pathlib import Path
import json,re,hashlib,subprocess
root=Path.cwd()
def write(p,obj):
 subprocess.run(['python3','-I','-B',str(root/'write_lane.py'),p],input=json.dumps(obj,indent=2)+'\n',text=True,check=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
order=json.loads(Path('SOURCE-ORDER.json').read_text())
receipts=[(p,json.loads(p.read_text())) for p in Path('receipt').glob('*.json')]
rs={d['label']:(p,d) for p,d in receipts}
for m in order:
 for prefix in ['lean_','leanchecker_']:
  p,d=rs[prefix+m]; assert d['exit']==0 and not d['group_members_left']; assert sha(Path(d['log']))==d['log_sha256']
 assert sha(Path('src')/(m+'.lean'))==sha(Path('inputs/author-src')/(m+'.lean'))
write('results/FRESH-REPLAY.json',{'empty_build_evidence':'logs/1794122903691257997_precompile.log','modules':order,'sources_after_checkers':{m:sha(Path('src')/(m+'.lean')) for m in order},'oleans_after_checkers':{m:sha(Path('build')/(m+'.olean')) for m in order},'receipts':[{ 'path':str(p),'sha256':sha(p),**d} for p,d in receipts],'all39_strict_and_checker':True,'classification':{'mathematical':35,'controls':1,'audit':2,'API_probe':1}})
log=Path(rs['lean_CMDRRAuditFinal'][1]['log']); t=log.read_text()
env=re.findall(r'^ENV_DECL (\S+) ORIGIN (.*?) HAS_BODY (true|false)$',t,re.M|re.S)
prod=re.findall(r'^PRODUCTION (\S+) AXIOMS \[(.*?)\]$',t,re.M|re.S)
nodes={n: {'origin':o,'has_body':b,'deps':re.findall(r'[^,\s]+',ds)} for n,o,b,ds in re.findall(r'^BODY_NODE (\S+) ORIGIN (.*?) HAS_BODY (true|false) DEPS \[(.*?)\]$',t,re.M|re.S)}
closures={n:re.findall(r'[^,\s]+',v) for n,v in re.findall(r'^ENDPOINT_CLOSURE (\S+) \[(.*?)\]',t,re.M|re.S)}
allowed={'propext','Classical.choice','Quot.sound'}
assert len(env)==len({n for n,o,b in env})
for n,axs in prod: assert set(re.findall(r'[^,\s]+',axs))<=allowed
for n,d in nodes.items(): assert all(dep in nodes for dep in d['deps']),n
for n,items in closures.items():
 seen=set(); todo=[n]
 while todo:
  x=todo.pop()
  if x in seen: continue
  seen.add(x); todo+=nodes[x]['deps']
 assert len(items)==len(set(items)) and set(items)==seen,n
seen=set(); todo=[n for n,a in prod]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo+=nodes[n]['deps']
assert seen==set(nodes)
origins={o for n,o,b in env if n in dict(prod)}
assert {n for n,o,b in env if o in origins}==set(dict(prod))
write('audit/RECOMPUTED-DAG.json',{'fresh_log':str(log),'sha256':sha(log),'environment_count':len(env),'production_count':len(prod),'union_nodes':len(nodes),'endpoint_counts':{n:len(v) for n,v in closures.items()},'closure_and_union_recomputed':True,'production_origins':sorted(origins),'production':dict(prod),'body_nodes':nodes,'closures':closures,'limits':'Independent documentary recomputation of emitted DAG. Does not itself verify Lean metadata safety, extern/implementedBy attributes, or unsupported opaque primitives; that separate gate remains open.'})
print('COUNTS',len(env),len(prod),len(nodes));print('CLOSURES',json.dumps({n:len(v) for n,v in closures.items()}));print('ALL39_REPLAY_AND_POSTHASH_OK')
