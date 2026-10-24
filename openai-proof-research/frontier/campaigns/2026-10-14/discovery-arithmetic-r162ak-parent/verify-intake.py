#!/usr/bin/env python3
"""Read-only byte and selected-input verification; no mathematical gate."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162ak'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def snapshot(root):
    result={}
    for f in root.rglob('*'):
        assert not f.is_symlink()
        if f.is_file():
            raw=f.read_bytes();result[f.relative_to(root).as_posix()]=dict(bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode)
    return result
before=json.loads((D/'private/intake/root-before.json').read_text())
assert len(before)==45 and snapshot(R)==before
anchors={'packet/FINAL.md':'d21cfd3f2e3ecaa4fc1c4e3b40ba02433b0720ec0c3d9df21ae9bd3d159bd3f9','packet/MANIFEST.json':'8e6f7256fe42576799f695d770c66fd0467202ebb494ef9a9515eba50afe1a7e','REPORT.md':'4408116fe79f131b30ac6baa3c457ac16fce6727bf0dcefb64d706dbc3475733'}
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
m=json.loads((R/'packet/MANIFEST.json').read_text());assert len(m['files'])==41
assert set(before)=={x['path'] for x in m['files']}|set(anchors)|{'ANCHORS.json'}
cmd=['python','-I','-B',str(R/'verify.py'),'--final-sha256',anchors['packet/FINAL.md'],'--manifest-sha256',anchors['packet/MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
v=json.loads(subprocess.check_output(cmd,cwd=P,text=True));assert v['payload_files']==41 and not v['mathematical_gate']
tree=json.loads((P/'sources/preprints-tree.json').read_text());entries=tree['tree'];by_path={x['path']:x for x in entries}
bindings=json.loads((R/'private/source/authentication.json').read_text());assert len(bindings)==11
for x in bindings:
    local=R/'private/source'/Path(x['path']).name;raw=local.read_bytes();entry=by_path[x['path']]
    assert len(raw)==x['bytes']==entry['size'] and sha(raw)==x['sha256']
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['git_blob']==entry['sha']
c=json.loads((R/'private/companion/authentication.json').read_text());raw=(R/'private/companion/independent-sets.pdf').read_bytes()
assert sha(raw)==c['sha256'] and len(raw)==by_path[c['path']]['size']
assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==c['git_blob']==by_path[c['path']]['sha']
old_inputs=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(old_inputs)==5
for x in old_inputs:
    f=P/x['path'];raw=f.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and f.stat().st_mode==x['mode']
assert snapshot(R)==before
out=dict(status='MATCH',payload_files=41,payload_bytes=sum(x['bytes'] for x in m['files']),whole_root_files=45,whole_root_bytes_and_full_modes_unchanged=True,exact_root_membership_checked=True,canonical_text_git_bindings_checked=11,companion_pdf_git_bindings_checked=1,completed_direct_inputs_unchanged=5,detached_anchors=anchors,copied_controls_checked=2,synthetic_mutations_not_rerun=True,artifact_check_only=True,correctness_gate=None,contribution_gate=None,count_change=0,parent_reading='Complete scope,REPORT,FINAL,MATH characters[0,11000),[11000,19792),READING-LIMITS and WORKING; no independent source or primary proof rereading.',limits='Child checks exact payload bytes/membership and anchors, not file modes; parent additionally checks exact45-file root membership and pre-read full modes. Only11 downloaded canonical text blobs and1 companion PDF are independently Git-authenticated; no claim all13 canonical folder blobs were fetched. No directory-identity or mathematical gate follows.')
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
