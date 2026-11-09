from pathlib import Path
import os,sys,subprocess,json
root=Path(__file__).resolve().parents[1]
build=Path(os.environ.get('BUILD_ROOT',str(root))).resolve()
os.chdir(root)
lean=Path(os.environ['LEAN_BIN']).resolve()
packages=Path(os.environ['LEAN_PACKAGES']).resolve()
env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN','LAKE'))}
env.update(LEAN_PATH=':'.join([str(build/'formal')]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]),MALLOC_ARENA_MAX='2',HOME=str(root/'empty-home'),TMPDIR=str(root/'tmp'),PYTHONDONTWRITEBYTECODE='1')
rc=subprocess.run([sys.executable,'-I','scripts/watchdog.py','logs/auditor-safety.log',str(lean),'-j1','-DwarningAsError=true','checks/AuditToolSafety.lean'],env=env).returncode
(root/'auditor-safety-receipt.json').write_text(json.dumps({'passed':rc==0,'exit_code':rc,'build_root':str(build),'log':'logs/auditor-safety.log'},indent=2)+'\n')
sys.exit(rc)
