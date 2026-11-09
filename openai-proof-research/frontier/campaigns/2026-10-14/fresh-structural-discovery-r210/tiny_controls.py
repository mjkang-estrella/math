"""One small copied-fixture exercise; never modifies source or the final selected packet."""
from pathlib import Path
import importlib.util,shutil,json,hashlib,os
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r210')
spec=importlib.util.spec_from_file_location('v',R/'verify_packet.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
C=R/'controls';C.mkdir(exist_ok=False);P=C/'packet';P.mkdir()
for n in ['FINAL.md','FROZEN-STATEMENT.md']:shutil.copyfile(R/n,P/n);os.chmod(P/n,0o644)
os.chmod(P,0o755)
report=C/'REPORT.md';report.write_text('Tiny copied artifact controls only; no mathematical gate.\n');os.chmod(report,0o644)
m={'format':'r210-exact-selected-packet-v1','final':'FINAL.md','entries':[dict(path=k,**val) for k,val in sorted(v.inspect(P).items())]}
manifest=C/'MANIFEST.json';manifest.write_text(json.dumps(m,indent=2)+'\n')
args=(P,manifest,v.sha(manifest),v.sha(P/'FINAL.md'),report,v.sha(report))
results=[]
def run(name,expect):
 try:v.verify(*args);passed=True
 except ValueError:passed=False
 assert passed==expect,(name,passed,expect)
 results.append({'control':name,'expected_acceptance':expect,'actual_acceptance':passed})
run('unaltered small copy',True)
p=P/'FINAL.md';b=p.read_bytes();p.write_bytes(b+b'changed');run('copied byte alteration',False);p.write_bytes(b)
x=P/'extra.txt';x.write_text('extra');run('unselected extra file',False);x.unlink()
os.chmod(p,0o600);run('copied mode alteration',False);os.chmod(p,0o644)
x=P/'FROZEN-STATEMENT.md';b=x.read_bytes();x.unlink();run('missing selected file',False);x.write_bytes(b);os.chmod(x,0o644)
run('restored small copy',True)
(R/'private/artifact-controls.json').write_text(json.dumps({'note':'Own new tiny fixture manifest, not an inherited manifest attached to a reduced source selection. Source originals unchanged. Artifact tests are not mathematical gates.','results':results},indent=2)+'\n')
print(json.dumps(results,indent=2))
