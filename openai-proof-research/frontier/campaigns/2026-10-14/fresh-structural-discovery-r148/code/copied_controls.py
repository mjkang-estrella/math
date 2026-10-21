"""One bounded fixture of selected own bytes, with its own membership manifest."""
from pathlib import Path
import hashlib,json,subprocess,sys
sys.dont_write_bytecode=True
from verify import inventory,digest
ROOT=Path(__file__).resolve().parents[1]
FIX=ROOT/'private/controls/reduced-copy'
if FIX.exists():raise SystemExit('Controls already exist; do not overwrite')
(FIX/'payload').mkdir(parents=True)
receipts=[]
for src in ['notes/01-prefreeze-calculations.md','code/diagnostic.py']:
    p=ROOT/src;target=FIX/'payload'/p.name;target.write_bytes(p.read_bytes())
    h=subprocess.check_output(['sha256sum',str(target)],text=True).split()[0]
    assert h==digest(p)
    receipts.append({'own_original':src,'own_original_bytes':p.stat().st_size,'own_original_sha256':digest(p),'reduced_copy':target.relative_to(FIX).as_posix(),'copy_independent_sha256sum':h})
(ROOT/'private/controls/source-copy-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
(FIX/'FINAL.md').write_text('Reduced artifact control only. No mathematical result.\n')
(FIX/'REPORT.md').write_text('Selected own note/code bytes; independent reduced membership. No copied original manifest.\n')
(FIX/'MANIFEST.json').write_text(json.dumps(inventory(FIX),indent=2,sort_keys=True)+'\n')
anchors={n:digest(FIX/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snapshot():
    return {'payload':inventory(FIX),'envelopes':{n:digest(FIX/n) for n in anchors},'verifier':digest(ROOT/'code/verify.py')}
results=[]
def run(label,expected,aa=None):
    h=anchors if aa is None else aa
    before=snapshot()
    cmd=[sys.executable,'-B',str(ROOT/'code/verify.py'),str(FIX),'--final',h['FINAL.md'],'--manifest',h['MANIFEST.json'],'--report',h['REPORT.md']]
    p=subprocess.run(cmd,capture_output=True,text=True,timeout=20)
    assert snapshot()==before,'Verifier mutated fixture'
    assert (p.returncode==0)==expected,(label,p.stdout,p.stderr)
    results.append({'case':label,'expected_accept':expected,'returncode':p.returncode,'output':json.loads(p.stdout),'read_only_snapshot_equal':True})
run('baseline',True)
p=FIX/'payload/01-prefreeze-calculations.md';original=p.read_bytes()
p.write_bytes(original+b'\naltered\n');run('altered payload',False);p.write_bytes(original)
p.unlink();run('missing payload',False);p.write_bytes(original)
p=FIX/'.extra-hidden';p.write_text('extra');run('extra hidden payload',False);p.unlink()
p=FIX/'extra-empty';p.mkdir();run('extra empty directory',False);p.rmdir()
for n in anchors:
    wrong=dict(anchors);wrong[n]=('0' if anchors[n][0]!='0' else '1')+anchors[n][1:]
    run('wrong detached '+n,False,wrong)
run('restored baseline',True)
(ROOT/'notes/control-results.json').write_text(json.dumps({'scope':'Artifact controls only; same research agent, not independent mathematical review.','fixture':'private/controls/reduced-copy','fixture_anchors':anchors,'results':results},indent=2)+'\n')
print(json.dumps({'cases':len(results),'all_expected_outcomes':True,'read_only':True}))
