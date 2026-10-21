#!/usr/bin/env python3
"""Read-only full-scope contribution intake; artifact checks are not math gates."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];R=B/'arithmetic-r147-contribution-r1'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'e94b8956298e206a4edaa211c5adf253ef2e7573c88778da385847e05189b5d7','MANIFEST.json':'3a93f20951c393afd3e927cdd8a9ee73237481763da9d17c3a59699778990a18','REPORT.md':'34ea2a8442afc456b22d25e9f2647f4a3de11654a51584c509cb3a5b354dff43'}
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);assert all(sha(R/p)==v for p,v in anchors.items())
    cmd=['python','-I','-B',str(R/'verify_packet.py'),'--root',str(R),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--originals-project',str(P)]
    run=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not run.stderr
    m=read(R/'MANIFEST.json');selected={x['path']for x in m['files']};assert len(selected)==len(m['files'])==56
    actual={p for p,x in before.items()if x['kind']=='file'};assert selected|{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}<=actual
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(R/'private/source-authentication.json')['sources'];assert len(bindings)==8
    for x in bindings:
        p=R/'private/source'/Path(x['path']).name;d=p.read_bytes();e=lookup[x['path']]
        assert len(d)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['blob']==e['sha']
    ranges=read(R/'private/original-anchors.json');direct=read(R/'private/immutable-inputs.json');assert len(ranges)==4 and len(direct)==18;stable={};modes={}
    for x in direct:
        p=P/x['path'];assert not p.is_symlink()and p.stat().st_nlink==1 and p.stat().st_size==x['bytes']and sha(p)==x['sha256']and stat.S_IMODE(p.stat().st_mode)==x['mode'];stable[x['path']]=x['sha256'];modes[x['path']]=x['mode']
    for x in ranges:
        p=P/x['path'];assert not p.is_symlink()and p.stat().st_nlink==1
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert len(data)==x['end']-x['start']and hashlib.sha256(data).hexdigest()==x['sha256']and data==(R/x['local']).read_bytes()and stat.S_IMODE(p.stat().st_mode)==x['mode'];modes[x['path']]=x['mode']
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['path']]=x['sha256']
    assert snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'author_validator_stdout':run.stdout.strip(),'payload_files':56,'exact_selected_membership_and_modes_checked':True,'whole_root_files':len(actual),'unselected_root_files':sorted(actual-selected-{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}),'canonical_objects':8,'canonical_matches_complete_pinned_tree':True,'explicit_original_checks':22,'whole_direct_original_records':18,'selected_history_intervals':4,'whole_history_original_records':1,'original_range_anchors':ranges,'stable_named_originals':stable,'stable_original_modes':modes,'entire_root_unchanged':True,'parent_semantic_reading':'Complete REVIEW in overlapping byte chunks, provisional private DERIVATIONS, FINAL, REPORT, READING-AND-ISOLATION and verifier. Terminal REVIEW completes all provisional primary/resolution/spreading/history checks. Source/primary reading attributed to reviewer; parent has not reread protected bodies. No live Analytic177 or Structural184 findings/status/activity read or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in ['payload_files','whole_root_files','unselected_root_files','canonical_objects','explicit_original_checks','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
