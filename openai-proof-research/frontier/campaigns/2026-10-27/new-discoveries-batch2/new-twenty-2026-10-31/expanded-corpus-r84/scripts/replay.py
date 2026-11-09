from pathlib import Path
import json,os,subprocess,zipfile,hashlib
D=Path(__file__).resolve().parents[1];F=D/'fresh-extracted';F.mkdir(exist_ok=True)
with zipfile.ZipFile(D/'hierarchy-packet.zip','w',compression=zipfile.ZIP_DEFLATED)as z:
 for f in ['lean/Hierarchy.lean','lean/Audit.lean','scripts/leanrun.py','scripts/limited.py','PACKET-README.md','DEPENDENCIES.json']:
  info=zipfile.ZipInfo(f,date_time=(2026,11,1,0,0,0));z.writestr(info,(D/f).read_bytes())
with zipfile.ZipFile(D/'hierarchy-packet.zip')as z:z.extractall(F)
root=Path('/home/mj-kang/Documents/Dev/math');bins=root/'dlp-research/.tools/lean-4.34.1-linux/bin';deps=root/'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
env={k:v for k,v in os.environ.items()if k not in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']};env['PATH']=str(bins)+':'+env.get('PATH','');env['LEAN_PATH']=str(F/'lean')+':'+':'.join(str(p)for p in deps.glob('*/.lake/build/lib/lean'));F.joinpath('logs').mkdir(exist_ok=True)
records=[]
for name,cmd in [('strict-build',[str(bins/'lean'),'-j1','-DwarningAsError=true','-o','lean/Hierarchy.olean','lean/Hierarchy.lean']),('full-audit',[str(bins/'lean'),'-j1','-DwarningAsError=true','lean/Audit.lean']),('checker',[str(bins/'leanchecker'),'-j1','Hierarchy'])]:
 run=subprocess.run(['python',str(F/'scripts/limited.py'),name,*cmd],cwd=F,env=env,check=True);records.append(json.loads((F/'logs'/f'{name}.receipt.json').read_text()));assert records[-1]['returncode']==0
(D/'outputs/fresh-replay.json').write_text(json.dumps({'packet_sha256':hashlib.sha256((D/'hierarchy-packet.zip').read_bytes()).hexdigest(),'steps':records,'trust_limit':'Local module freshly compiled, all local declarations audited and leanchecker replayed from imports; cached pinned upstream dependencies not rebuilt.'},indent=2)+'\n')
