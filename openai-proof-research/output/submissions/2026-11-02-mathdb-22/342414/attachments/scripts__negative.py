from pathlib import Path
import os,sys,subprocess,json
root=Path(__file__).resolve().parents[1];os.chdir(root)
lean=Path(os.environ['LEAN_BIN']).resolve();packages=Path(os.environ['LEAN_PACKAGES']).resolve()
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env.update(LEAN_PATH=':'.join([str(root/'formal')]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]),MALLOC_ARENA_MAX='2',HOME=str(root/'empty-home'),TMPDIR=str(root/'tmp'),PYTHONDONTWRITEBYTECODE='1')
results=[]
for p in sorted((root/'negative-controls').glob('*.lean')):
 log='logs/negative-'+p.stem+'.log'
 rc=subprocess.run([sys.executable,'-I','scripts/watchdog.py',log,str(lean),'-j1','-DwarningAsError=true',str(p)],env=env).returncode
 receipt=json.loads(Path(log+'.receipt.json').read_text())
 # A timeout or resource kill is not an expected rejection.
 results.append({'name':p.stem,'exit_code':rc,'rejected':rc==1 and receipt['killed'] is None and 'error:' in Path(log).read_text()})
# Verify that the replay refuses preexisting compiled files.
r=subprocess.run([sys.executable,'-I','scripts/replay.py'],capture_output=True,text=True,env=os.environ.copy())
(root/'logs/negative-existing-olean.log').write_text(r.stdout+r.stderr)
results.append({'name':'existing-olean','exit_code':r.returncode,'rejected':r.returncode!=0 and 'REFUSED: existing .olean' in r.stderr})
(root/'negative-results.json').write_text(json.dumps({'checks':results,'passed':all(x['rejected'] for x in results)},indent=2)+'\n')
sys.exit(0 if all(x['rejected'] for x in results) else 1)
