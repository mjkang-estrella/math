import os,sys,json,time,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent.parent
T=Path(sys.argv[1]).resolve(); mode=sys.argv[2] if len(sys.argv)>2 else 'build'
assert T.is_relative_to(L)
for d in ['logs','build','tmp/cache']:(T/d).mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env.update(TMPDIR=str(T/'tmp'),XDG_CACHE_HOME=str(T/'tmp/cache'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
bin='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'
env['PATH']=bin+':'+env['PATH']
pkg=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env['LEAN_PATH']=':'.join([str(T/'build')]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))])
def run(tag,args):
 name=tag+'-'+str(time.time_ns());env['ULAS_AUDIT_OUT']=str(T/'logs'/('frozen-'+name+'.jsonl'));env['ULAS_AUDIT_SHARD']='0'
 if tag.startswith('audit-shard-'):
  shard=tag.rsplit('-',1)[1];env['ULAS_AUDIT_OUT']=str(T/'logs'/('declarations-'+shard+'.jsonl'));env['ULAS_AUDIT_SHARD']=shard
 print(name,flush=True)
 cmd=['bash','-c','ulimit -t 120; exec taskset -c 0,1 timeout -k 2 140 /usr/bin/time -v python3 -I "$@"','runner',str(L/'scripts/bounded.py')]+args
 with open(T/'logs'/(name+'.log'),'w') as out,open(T/'logs'/(name+'.stderr'),'w') as err:
  r=subprocess.run(cmd,cwd=T/'src',env=env,stdout=out,stderr=err)
 (T/'logs'/(name+'.result.json')).write_text(json.dumps(dict(args=args,exit_code=r.returncode)))
 if r.returncode:raise SystemExit('FAILED '+name)
order=json.loads((L/'module-order.json').read_text())
if mode=='build':
 for m in order:
  mark=T/'logs'/('build-'+m+'.done')
  if mark.exists():continue
  run('build-'+m,['lean','-j1','-M3500','-DwarningAsError=true','-o',str(T/'build'/(m+'.olean')),m+'.lean']);mark.touch()
elif mode=='checker':
 for m in order:
  mark=T/'logs'/('checker-'+m+'.done')
  if mark.exists():continue
  run('checker-'+m,['leanchecker',m]);mark.touch()
elif mode=='audit':
 for i in range(8):
  mark=T/'logs'/('audit-'+str(i)+'.done')
  if mark.exists():continue
  run('audit-shard-'+str(i),['lean','-j1','-M3500','-DwarningAsError=true',str(L/'scripts/audit-final.lean')]);mark.touch()
 run('audit-analysis',['python3','-I',str(L/'scripts/analyze-final.py'),str(T/'logs/declarations-*.jsonl'),str(T/'logs/audit-summary.json')])
elif mode=='controls':
 for f in sorted(list((T/'scripts').glob('*Negative*.lean')) + list((T/'scripts').glob('negative-*.lean'))):
  # Expected rejection: preserve complete output, assert a type mismatch.
  try:run('negative-'+f.stem,['lean','-j1','-M3500','-DwarningAsError=true',str(f)])
  except SystemExit:
   logs=sorted((T/'logs').glob('negative-'+f.stem+'-*.log'));s=logs[-1].read_text();assert 'Type mismatch' in s or 'type mismatch' in s,s
  else:raise AssertionError('Control unexpectedly passed: '+str(f))
