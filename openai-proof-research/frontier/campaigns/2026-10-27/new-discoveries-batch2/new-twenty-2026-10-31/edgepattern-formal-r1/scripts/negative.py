from pathlib import Path
import os,subprocess,sys,json
root=Path(__file__).resolve().parents[1];os.chdir(root)
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
pkgs=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(root/'extracted/formal')]+[str(p/'.lake/build/lib/lean') for p in pkgs.iterdir() if (p/'.lake/build/lib/lean').is_dir()])
checks=[]
for name in ['FalseValue','FalseIndependent','FalseBound']:
 log='negative-controls/'+name+'.log'
 rc=subprocess.run([sys.executable,'-I','scripts/watchdog.py',log,str(lean),'-j1','-DwarningAsError=true','negative-controls/'+name+'.lean'],env=env).returncode
 text=Path(log).read_text(); rejected=rc==1 and ('error:' in text)
 checks.append(dict(control=name,exit_code=rc,rejected=rejected))
p=subprocess.run([sys.executable,'-I','extracted/scripts/replay.py'],env=env,capture_output=True,text=True)
Path('negative-controls/existing-olean.log').write_text(p.stdout+p.stderr)
checks.append(dict(control='existing-olean refusal',exit_code=p.returncode,rejected=p.returncode!=0 and 'REFUSED' in p.stderr))
Path('negative-controls/results.json').write_text(json.dumps({'checks':checks,'passed':all(x['rejected'] for x in checks)},indent=2)+'\n')
sys.exit(0 if all(x['rejected'] for x in checks) else 1)
