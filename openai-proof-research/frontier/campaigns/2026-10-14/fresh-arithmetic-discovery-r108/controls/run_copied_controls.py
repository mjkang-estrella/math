"""Bounded copied artifact controls. All writes are under the assigned r108 root."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys
import verify
ROOT=Path(__file__).resolve().parents[1]
copy=ROOT/'scratch/copied-controls/baseline'
assert not copy.exists(), 'Preserve an existing control run instead of overwriting it'
copy.mkdir(parents=True)
files=verify.inventory(ROOT)
for rel in files:
 dst=copy/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/rel,dst)
(copy/'FINAL.md').write_text('Copied verifier fixture FINAL, not mathematical handoff.\n')
(copy/'REPORT.md').write_text('Copied verifier fixture REPORT, not an independent review.\n')
(copy/'MANIFEST.json').write_text(json.dumps({'format':'r108-exact-v1','outside_files':sorted(verify.OUTSIDE),'omitted_subtree':verify.OMIT,'files':verify.inventory(copy)},indent=2)+'\n')
anchors={n:verify.sha((copy/n).read_bytes()) for n in ['MANIFEST.json','FINAL.md','REPORT.md']}
args=[sys.executable,'-B',str(copy/'controls/verify.py'),'--root',str(copy),'--manifest-sha',anchors['MANIFEST.json'],'--final-sha',anchors['FINAL.md'],'--report-sha',anchors['REPORT.md']]
results=[]
def test(name,expected):
 before=verify.inventory(copy)
 p=subprocess.run(args,capture_output=True,text=True,timeout=20)
 after=verify.inventory(copy)
 assert before==after,'Verifier changed payload'
 assert p.returncode==expected,(name,p.returncode,p.stderr)
 results.append({'control':name,'expected_exit':expected,'actual_exit':p.returncode,'payload_read_only':True,'diagnostic':p.stderr.strip()})
test('unchanged full copied payload',0)
target=copy/'notes/visibility-feasibility.md';original=target.read_bytes()
target.write_bytes(original+b'\nmutation\n');test('changed payload bytes',1);target.write_bytes(original)
extra=copy/'private/.unexpected.json';extra.write_text('{}');test('unexpected hidden JSON payload',1);extra.unlink()
target.unlink();test('missing payload file',1);target.write_bytes(original)
for name in ['FINAL.md','REPORT.md','MANIFEST.json']:
 p=copy/name;original=p.read_bytes();p.write_bytes(original+b'\n');test('changed '+name+' against detached anchor',1);p.write_bytes(original)
symlink=copy/'private/unexpected-link';symlink.symlink_to('../READING.md')
# Inventory itself rejects symlinks; run verifier directly for this control.
p=subprocess.run(args,capture_output=True,text=True,timeout=20)
assert p.returncode==1 and symlink.is_symlink();results.append({'control':'unexpected payload symlink','expected_exit':1,'actual_exit':p.returncode,'payload_read_only':True,'diagnostic':p.stderr.strip()});symlink.unlink()
test('restored copied payload',0)
(ROOT/'notes/copied-control-results.json').write_text(json.dumps({'scope':'Artifact controls only; fixture anchors are not final anchors. No mathematical gate. All mutation targets are copies.','controls':results},indent=2)+'\n')
print(json.dumps({'controls':len(results),'all_observed_expected':True,'copy':str(copy.relative_to(ROOT))}))
