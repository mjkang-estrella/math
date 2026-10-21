"""Create the actual payload manifest once, then read-only verification and independent hashes."""
from pathlib import Path
import json,os,importlib.util,subprocess,sys
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r164')
sp=importlib.util.spec_from_file_location('verify',R/'tools/verify_packet.py');v=importlib.util.module_from_spec(sp);sp.loader.exec_module(v)
assert not (R/'MANIFEST.json').exists(),'actual root has already been sealed'
for n in ['FINAL.md','REPORT.md']:os.chmod(R/n,0o644)
files,dirs=v.inventory(R)
m={'schema':'r164-exact-selection-v1','files':files,'directories':dirs,'envelope_modes':{n:0o644 for n in v.ENV},'scope':'Own exact selected payload only; incoming identities do not imply original whole-packet membership. Mathematical gates unassigned.'}
with (R/'MANIFEST.json').open('x') as f:f.write(json.dumps(m,indent=2,sort_keys=True)+'\n')
os.chmod(R/'MANIFEST.json',0o644)
anchors={n:v.sha((R/n).read_bytes()) for n in sorted(v.ENV)}
print(json.dumps({'root':str(R.resolve()),'detached_anchors':anchors,'read_only_verification':v.verify(R,anchors)},indent=2))
x=subprocess.run(['sha256sum',str(R/'FINAL.md'),str(R/'MANIFEST.json'),str(R/'REPORT.md')],capture_output=True,text=True,check=True,timeout=10)
for line in x.stdout.splitlines():
 digest,path=line.split(None,1);assert anchors[Path(path).name]==digest
print('INDEPENDENT sha256sum agrees with hashlib for all three outside envelopes.')
print(x.stdout,end='')
