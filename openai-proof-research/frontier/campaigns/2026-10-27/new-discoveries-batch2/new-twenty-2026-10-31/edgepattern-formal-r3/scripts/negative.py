from pathlib import Path
import os,sys,subprocess,json
root=Path(__file__).resolve().parents[1];os.chdir(root)
proof_root=root/'extracted' if (root/'extracted/formal').is_dir() else root
(root/'empty-home').mkdir(exist_ok=True)
(root/'tmp').mkdir(exist_ok=True)
lean=Path(os.environ['LEAN_BIN']).resolve();pkgs=Path(os.environ['LEAN_PACKAGES']).resolve()
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env.update(LEAN_PATH=':'.join([str(proof_root/'formal')]+[str(p/'.lake/build/lib/lean') for p in sorted(pkgs.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]),HOME=str(root/'empty-home'),TMPDIR=str(root/'tmp'),MALLOC_ARENA_MAX='2',PYTHONDONTWRITEBYTECODE='1')
checks=[]
for n in ['FalseExpectation','FalseGirth','FalseIndependent','FalseMask','FalseTotals','FalseCanonicalBound','FalseBlockCertificate']:
 log='negative-controls/'+n+'.log'
 rc=subprocess.run([sys.executable,'-I','scripts/watchdog.py',log,str(lean),'-j1','-DwarningAsError=true','negative-controls/'+n+'.lean'],env=env).returncode
 s=Path(log).read_text()
 checks.append(dict(name=n,exit_code=rc,rejected=rc==1 and 'error:' in s and 'unknown module' not in s and 'unknown identifier' not in s and 'unknown constant' not in s))
p=subprocess.run([sys.executable,'-I',str(proof_root/'scripts/replay.py')],env=os.environ.copy(),capture_output=True,text=True)
Path('negative-controls/existing-olean.log').write_text(p.stdout+p.stderr)
checks.append(dict(name='existing-olean refusal',exit_code=p.returncode,rejected=p.returncode!=0 and 'REFUSED' in p.stderr))
Path('negative-controls/results.json').write_text(json.dumps(dict(checks=checks,passed=all(c['rejected'] for c in checks)),indent=2)+'\n')
sys.exit(0 if all(c['rejected'] for c in checks) else 1)
