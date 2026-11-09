"""Resumable strict source-only replay. Run --init once, then --resume --steps N."""
import argparse, hashlib, json, pathlib, subprocess, sys, zipfile, time
D=pathlib.Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(s): (D/'replay-state.json').write_text(json.dumps(s,indent=2)+'\n')
p=argparse.ArgumentParser();p.add_argument('--init',action='store_true');p.add_argument('--resume',action='store_true');p.add_argument('--steps',type=int,default=1);a=p.parse_args()
Z=D/'pdtar-source.zip'; E=D/'replay/extracted'
if a.init:
 if (D/'replay-state.json').exists() or E.exists(): raise SystemExit('refusing existing replay')
 E.mkdir(parents=True)
 with zipfile.ZipFile(Z) as z:
  names=z.namelist()
  assert len(names)==len(set(names))
  for n in names:
   q=pathlib.PurePosixPath(n)
   assert not q.is_absolute() and '..' not in q.parts and not n.endswith(('.olean','.ilean','.ir'))
  z.extractall(E)
 (E/'tmp').mkdir();(E/'logs').mkdir()
 s=dict(zip_sha256=sha(Z),next=0,objects={},steps=[]);save(s)
 print('Initialized fresh extraction');sys.exit(0)
assert a.resume
s=json.loads((D/'replay-state.json').read_text());assert sha(Z)==s['zip_sha256']
with zipfile.ZipFile(Z) as z:
 assert (E/'manifest.json').read_bytes()==z.read('manifest.json'), 'manifest mismatch'
m=json.loads((E/'manifest.json').read_text())
for entry in s['steps']:
 assert sha(E/'logs'/(entry['name']+'.log'))==entry['log_sha256'], 'log mismatch'
mods=m['modules']; jobs=[('build-'+x,['scripts/compile.py','-o','PDTAR/'+x+'.olean','PDTAR/'+x+'.lean'],False) for x in mods]
jobs += [('check-'+x,['scripts/check.py','PDTAR.'+x],False) for x in mods]
jobs += [('audit',['scripts/compile.py','scripts/Audit.lean'],False)]
jobs += [(x,['scripts/compile.py','scripts/'+x+'.lean'],True) for x in ['NegK23', 'NegK34', 'NegEndpointTwo', 'NegFort', 'NegCorruptedFamily']]
for _ in range(a.steps):
 for f,h in m['files'].items(): assert sha(E/f)==h, 'source hash mismatch '+f
 for f,h in m['pins'].items(): assert sha(pathlib.Path(f))==h, 'pin mismatch '+f
 objs={str(x.relative_to(E)):sha(x) for x in E.rglob('*') if x.is_file() and any(k in x.name for k in ['.olean','.ilean','.ir'])}
 assert objs==s['objects'], 'unrecorded, missing or altered build objects'
 if s['next']==len(jobs): print('REPLAY COMPLETE');break
 base,cmd,negative=jobs[s['next']]
 name=str(time.time_ns())+'-'+base
 rc=subprocess.run([sys.executable,'-I',str(E/'scripts/limited.py'),name,sys.executable,'-I']+cmd,cwd=E).returncode
 log=(E/'logs'/f'{name}.log').read_text()
 ok=(rc!=0 and 'error:' in log and 'unsolved goals' in log or rc!=0 and 'error:' in log and 'Type mismatch' in log) if negative else rc==0
 if not ok: raise SystemExit('step failed: '+name)
 if base=='audit': assert 'AUDIT_TOTAL' in log and 'violations 0' in log
 s['objects']={str(x.relative_to(E)):sha(x) for x in E.rglob('*') if x.is_file() and any(k in x.name for k in ['.olean','.ilean','.ir'])}
 s['steps'].append(dict(name=name,returncode=rc,log_sha256=sha(E/'logs'/f'{name}.log')));s['next']+=1;save(s)
 print('PASS',name)
print('Progress',s['next'],'/',len(jobs))
