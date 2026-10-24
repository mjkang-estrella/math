#!/usr/bin/env python3
"""Read-only packet and input consistency checks; no mathematical gate."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162am'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def snapshot(root):
    out={}
    for f in root.rglob('*'):
        assert not f.is_symlink()
        if f.is_file():
            raw=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode)
    return out
before=json.loads((D/'private/intake/root-before.json').read_text());assert len(before)==77 and snapshot(R)==before
anchors={'private/FINAL.md':'4d3ac4e022098ceef51883d48f1eaeb5c25379bb7271b757b7e5fa56c31f2c71','private/MANIFEST.json':'d4e3deb52457cb01fb3f8fbb9624d1c81ef892391c6585a75fe5bcb5f8a9676d','REPORT.md':'6a9ba21ebc5026b1068135ddaa1131f2bbe5f9fba99c32e36f117ea9b6542c75'}
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
m=json.loads((R/'private/MANIFEST.json').read_text());assert len(m['files'])==74
assert set(before)=={'private/'+x['path'] for x in m['files']}|{'private/MANIFEST.json','REPORT.md','ANCHORS.json'}
def command(packet,report,a):return ['python','-I','-B',str(R/'private/verify.py'),'--packet',str(packet),'--report',str(report),'--final-sha256',a[0],'--manifest-sha256',a[1],'--report-sha256',a[2]]
a=[anchors['private/FINAL.md'],anchors['private/MANIFEST.json'],anchors['REPORT.md']]
stdout=subprocess.check_output(command(R/'private',R/'REPORT.md',a),cwd=P,text=True);assert '74 exact files' in stdout
tree=json.loads((P/'sources/preprints-tree.json').read_text());by_path={x['path']:x for x in tree['tree']};counts={}
for group,count in [('source',17),('companion',9),('tensor',11)]:
    rows=json.loads((R/f'private/{group}/access.json').read_text());assert len(rows)==count
    ownfiles=[f for f in (R/f'private/{group}').rglob('*') if f.is_file()]
    hashes={sha(f.read_bytes()):f for f in ownfiles}
    for x in rows:
        f=hashes[x['sha256']];raw=f.read_bytes();e=by_path[x['path']]
        assert len(raw)==x['bytes']==e['size']
        assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x.get('git_blob',x.get('blob'))==e['sha']
    counts[group]=count
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(inputs)==5
for x in inputs:
    f=P/x['path'];raw=f.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and f.stat().st_mode==x['mode']
ctl=R/'private/controls';fa=[sha((ctl/'original/FINAL.md').read_bytes()),sha((ctl/'original/MANIFEST.json').read_bytes()),sha((ctl/'REPORT.md').read_bytes())]
for name in ['original','copied']:
    result=subprocess.run(command(ctl/name,ctl/'REPORT.md',fa),cwd=P,capture_output=True,text=True);assert result.returncode==0
wrong=fa.copy();wrong[0]='0'*64
assert subprocess.run(command(ctl/'copied',ctl/'REPORT.md',wrong),cwd=P,capture_output=True).returncode!=0
historical=json.loads((ctl/'results.json').read_text());assert len(historical)==4 and all(x['exit']==x['expected_exit'] for x in historical)
assert snapshot(R)==before
out=dict(status='MATCH',manifest_files=74,manifest_bytes=sum(x['bytes'] for x in m['files']),whole_root_files=77,whole_root_bytes_and_full_modes_unchanged=True,exact_root_membership_checked=True,canonical_git_bindings_checked=counts,completed_direct_inputs_unchanged=5,readonly_copied_controls_replayed=3,historical_mutation_control_records=4,synthetic_mutations_not_rerun=True,detached_anchors=anchors,parent_reading='Complete FINAL,REPORT,MATH,SOURCE-COMPARISON,READING-LIMITS,WORKING and verifier;no independent canonical or primary proof rereading.',limits='Child checks74 private files and exact membership plus detached report;parent additionally checks77 whole-root identities/full modes,37 downloaded Git bindings and5 original completed inputs. Authentication of11 tensor objects is distinct from semantic reading of only5 complete text bodies. No directory-identity or mathematical gate follows.',artifact_check_only=True,correctness_gate=None,contribution_gate=None,count_change=0)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
