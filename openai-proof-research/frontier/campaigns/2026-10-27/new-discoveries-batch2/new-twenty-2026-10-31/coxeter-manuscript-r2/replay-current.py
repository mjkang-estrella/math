from pathlib import Path
import subprocess,os,json,hashlib
w=Path(__file__).resolve().parent;os.chdir(w)
m=json.loads((w/'packet-manifest.json').read_text())
for n,h in m.items():assert hashlib.sha256((w/'proof'/n).read_bytes()).hexdigest()==h
build=w/'authorized-replay';assert not build.exists();build.mkdir()
logs=w/'authorized-replay-logs';logs.mkdir()
bin=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
pkgs=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
os.environ['LEAN_PATH']=':'.join([str(build)]+[str(p/'.lake/build/lib/lean') for p in sorted(pkgs.iterdir()) if p.is_dir()])
for mod in (w/'reviews/replay-fit-r2/modules.txt').read_text().split():
 for kind,cmd in [('build',[str(bin/'lean'),'-j2','-M3500','-DwarningAsError=true','-o',str(build/(mod+'.olean')),str(w/'proof'/(mod+'.lean'))]),('check',[str(bin/'leanchecker'),mod])]:
  with (logs/(mod+'-'+kind+'.log')).open('w') as log:
   subprocess.run(['python3','-I',str(w/'run-capped.py'),'authorized-'+mod+'-'+kind]+cmd,stdout=log,stderr=subprocess.STDOUT,check=True)
