#!/usr/bin/env python3
"""Read-only Arithmetic150 selected-packet intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r150'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'4fca5d18fc84f48c0b17a1b1f8882a282b0db0759da357a7376b5b473cae5a84','MANIFEST.json':'a83f4fd11b8fad957a17126cbea027be377b36adba052c5002542adb3e949765','REPORT.md':'9975a42f48ddb83082910437f530657065c6c48acd37645a16d3d43a58f77db4'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    run=subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--original-project',str(P)],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    m=read(A/'MANIFEST.json');selected={x['path']for x in m['files']};assert len(selected)==len(m['files'])==62 and {p for p,x in before.items()if x['kind']=='file'}==selected|{'MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(A/'private/source-bindings.json');assert len(bindings)==11
    for x in bindings:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert len(d)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['sha']==e['sha']
    ranges=read(A/'private/original-extents.json');assert len(ranges)==12;stable={};modes={};whole=0
    for x in ranges:
        p=P/x['path'];assert not p.is_symlink()and p.stat().st_nlink==1
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert len(data)==x['end']-x['start']and hashlib.sha256(data).hexdigest()==x['sha256'];modes[x['path']]=stat.S_IMODE(p.stat().st_mode)
        if 'copy'in x:
            c=A/x['copy']if '/'in x['copy']else A/'private/originals'/x['copy'];assert data==c.read_bytes()
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['path']]=x['sha256'];whole+=1
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'author_validator_stdout':run.stdout.strip(),'payload_files':62,'exact_whole_root_membership_and_modes_checked':True,'canonical_objects':11,'canonical_matches_complete_pinned_tree':True,'original_range_anchors':ranges,'explicit_original_ranges':12,'whole_original_records':whole,'selected_history_intervals':2,'completed_exception_records':6,'stable_named_originals':stable,'stable_original_modes':modes,'original_modes_observed_at_parent_intake_not_initial_child_reads':True,'entire_root_unchanged':True,'parent_semantic_reading':'Complete PREFREEZE, DERIVATIONS including full central potential, joint budget, nonlinear Levi and radial optimum, UNRESOLVED, FINAL, REPORT, READING and verifier. Source/primary operative reading attributed to child, not fresh parent protected-body reading. No live Structural185/Arithmetic151 bodies/findings/status/activity inspected or steered; incoming Structural185 notified terminal archived separately without full intake.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['payload_files','canonical_objects','explicit_original_ranges','whole_original_records','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
