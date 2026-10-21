#!/usr/bin/env python3
"""Read-only Arithmetic148 selected-packet intake; no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r148'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'5ee48009ce1564092dbde918e0f50db7d3db335dbf063ec509928e876aff563d','MANIFEST.json':'38a45db3cefab309c789b73447c09a43f327fcf7e07872aa6b068189c26e7961','REPORT.md':'052675634aed424a3ba6847bec96c1a062f3bac308496e8f5f6913c996a285d8'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    run=subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--project',str(P)],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    m=read(A/'MANIFEST.json');selected={x['path']for x in m['files']};assert len(selected)==len(m['files'])==70 and {p for p,x in before.items()if x['kind']=='file'}==selected|{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(A/'private/source-bindings.json');assert len(bindings)==8
    for x in bindings:
        p=A/x['path'];d=p.read_bytes();e=lookup[x['upstream_path']];assert len(d)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']
    ranges=read(A/'private/original-anchors.json');assert len(ranges)==19;stable={};modes={};whole=0
    for x in ranges:
        p=P/x['path'];assert not p.is_symlink()and p.stat().st_nlink==1
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert len(data)==x['end']-x['start']and hashlib.sha256(data).hexdigest()==x['sha256'];modes[x['path']]=stat.S_IMODE(p.stat().st_mode)
        if 'copy'in x:
            c=A/x['copy']if '/'in x['copy']else A/'private/originals'/x['copy'];assert data==c.read_bytes()
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['path']]=x['sha256'];whole+=1
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'author_validator_stdout':run.stdout.strip(),'payload_files':70,'exact_whole_root_membership_and_modes_checked':True,'canonical_objects':8,'canonical_matches_complete_pinned_tree':True,'original_range_anchors':ranges,'explicit_original_ranges':19,'whole_original_records':whole,'selected_history_intervals':6,'completed_exception_records':9,'stable_named_originals':stable,'stable_original_modes':modes,'original_modes_observed_at_parent_intake_not_initial_child_reads':True,'entire_root_unchanged':True,'parent_semantic_reading':'Complete PREFREEZE, DERIVATIONS including late published-primary completion, UNRESOLVED, FINAL, REPORT, READING and verifier. Source/primary operative reading attributed to child, not fresh parent protected-body reading. No live Structural185/Arithmetic149 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['payload_files','canonical_objects','explicit_original_ranges','whole_original_records','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
