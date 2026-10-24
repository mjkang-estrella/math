#!/usr/bin/env python3
"""Read-only exact artifact/input checks; no correctness or contribution gate."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162an'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def snapshot(root):
    out={}
    for f in root.rglob('*'):
        assert not f.is_symlink()
        if f.is_file():
            raw=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode)
    return out
before=json.loads((D/'private/intake/root-before.json').read_text());assert len(before)==66 and snapshot(R)==before
anchors={'private/FINAL.md':'43dcfc866181846c86a686df9cd2c9daf788a3d365e1121440cd9fbb270205bf','private/MANIFEST.json':'31e66cc787a9ef530c6672fd7a6d9345874aa12ff0440afa9b2614acd00154d1','REPORT.md':'45f90ebeb458b2a0cb32ba79a21a4646883e30b673d315bb23690c317c5d8219'}
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
m=json.loads((R/'private/MANIFEST.json').read_text());assert len(m['files'])==63
assert set(before)=={'private/'+x['path'] for x in m['files']}|{'private/MANIFEST.json','REPORT.md','ANCHORS.json'}
def command(packet,report,a):return ['python','-I','-B',str(R/'private/verify_packet.py'),'--packet',str(packet),'--manifest',str(packet/'MANIFEST.json'),'--final',str(packet/'FINAL.md'),'--report',str(report),'--final-sha256',a[0],'--manifest-sha256',a[1],'--report-sha256',a[2]]
a=[anchors['private/FINAL.md'],anchors['private/MANIFEST.json'],anchors['REPORT.md']]
stdout=subprocess.check_output(command(R/'private',R/'REPORT.md',a),cwd=P,text=True);assert 'BYTE INTEGRITY ONLY' in stdout
tree=json.loads((P/'sources/preprints-tree.json').read_text());by_path={x['path']:x for x in tree['tree']}
rows=json.loads((R/'private/access.json').read_text());assert len(rows)==25
for x in rows:
    f=R/'private'/x['local'];assert f.is_relative_to(R/'private');raw=f.read_bytes();e=by_path[x['path']]
    assert len(raw)==x['bytes']==e['size'] and sha(raw)==x['sha256']
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['git_blob']==e['sha']
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(inputs)==5
for x in inputs:
    f=P/x['path'];raw=f.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and f.stat().st_mode==x['mode']
ctl=R/'private/control-tests';fa=[sha((ctl/'original/FINAL.md').read_bytes()),sha((ctl/'original/MANIFEST.json').read_bytes()),sha((ctl/'REPORT.txt').read_bytes())]
controls=[]
for name,ok in [('original',True),('good-copy',True),('corrupt-copy',False)]:
    result=subprocess.run(command(ctl/name,ctl/'REPORT.txt',fa),cwd=P,capture_output=True,text=True);assert (result.returncode==0)==ok
    controls.append(dict(fixture=name,accepted=result.returncode==0,as_expected=True))
wrong=fa.copy();wrong[1]='0'*64
assert subprocess.run(command(ctl/'good-copy',ctl/'REPORT.txt',wrong),cwd=P,capture_output=True).returncode!=0
assert snapshot(R)==before
out=dict(status='MATCH',manifest_files=63,manifest_bytes=sum(x['bytes'] for x in m['files']),whole_root_files=66,whole_root_bytes_and_full_modes_unchanged=True,exact_root_membership_checked=True,canonical_text_git_bindings_checked=25,completed_direct_inputs_unchanged=5,readonly_copied_controls=controls,wrong_anchor_rejected=True,synthetic_mutations_not_rerun=True,detached_anchors=anchors,parent_reading='Complete FINAL,REPORT,MATH characters[0,13000),[13000,24266),SOURCE-COMPARISON,READING-LIMITS,WORKING and verifier;no independent source/primary proof rereading.',limits='Child verifies exact63 private payload files plus3 detached anchors;parent additionally checks66 whole-root file identities/full modes,25 downloaded Git bindings and5 unchanged direct inputs. No directory-identity or mathematical gate follows.',workdir_deviation='Child disclosed one read-only own-notes command in its own packet workdir;no broader access or mutation reported.',artifact_check_only=True,correctness_gate=None,contribution_gate=None,count_change=0)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
