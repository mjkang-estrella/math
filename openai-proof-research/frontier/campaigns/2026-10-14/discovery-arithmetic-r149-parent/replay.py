#!/usr/bin/env python3
"""Read-only Arithmetic149 discovery intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r149'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'packet/FINAL.md':'365adeb74ad87838da34f1396d95e4f95ddf5044dd30bf747e2be0a1e1198b05','packet/MANIFEST.json':'21fdef17827bfe95f7829fb0a0e2bdc7ae6b4a9dc3397aa037f6da546c77952e','REPORT.md':'0f8d49b460e1f6aab6ff743e99a1d71e5681a4a281d66427f7a47df845583ceb'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    run=subprocess.run(['python','-I','-B',str(A/'verify.py'),'--packet',str(A/'packet'),'--manifest-sha256',anchors['packet/MANIFEST.json'],'--final-sha256',anchors['packet/FINAL.md'],'--report',str(A/'REPORT.md'),'--report-sha256',anchors['REPORT.md'],'--working-root',str(A),'--project-root',str(P)],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    m=read(A/'packet/MANIFEST.json');assert len(m['files'])==57
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(A/'private/source-bindings.json');assert len(bindings)==8
    for x in bindings:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(A.resolve())and len(d)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']
    ranges=read(A/'private/history-extents.json');assert len(ranges)==3;stable={};modes={}
    for x in ranges:
        p=P/x['path'];assert not p.is_symlink()and p.stat().st_nlink==1
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert len(data)==x['end']-x['start']and hashlib.sha256(data).hexdigest()==x['sha256']and data==(P/x['local']).read_bytes();modes[x['path']]=stat.S_IMODE(p.stat().st_mode)
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['path']]=x['sha256']
    completed=read(A/'private/completed-bindings.json');assert len(completed)==5
    for x in completed:
        p=P/x['path'];c=A/x['local'];assert p.stat().st_size==x['bytes']and sha(p)==sha(c)==x['sha256']and stat.S_IMODE(p.stat().st_mode)==int(x['mode'],8);stable[x['path']]=x['sha256'];modes[x['path']]=stat.S_IMODE(p.stat().st_mode)
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'author_validator_stdout':run.stdout.strip(),'payload_files':57,'exact_selected_membership_and_working_counterparts_checked':True,'canonical_objects':8,'canonical_matches_complete_pinned_tree':True,'original_range_anchors':ranges,'selected_history_intervals':3,'selected_history_original_bodies':2,'completed_exception_records':5,'stable_named_originals':stable,'stable_original_modes':modes,'original_modes_observed_at_final_child_check_or_parent_intake_not_initial_reads':True,'entire_root_unchanged':True,'parent_semantic_reading':'Complete three operative/dynamical/convex-limit notes, FINAL, REPORT, READING-ISOLATION and verifier. Source and primary operative reading attributed to child, not fresh parent protected-body reading. No live Structural185/Arithmetic150 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['payload_files','canonical_objects','selected_history_intervals','completed_exception_records','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
