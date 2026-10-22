#!/usr/bin/env python3
"""Read-only Arithmetic152 r2 recovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r152'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'8ab8b5a527f66265a132c1343aee4a5feb0bf2adfabb8e80c0223e0c88ce191a','MANIFEST.json':'1630ccb39e2e5dad332f0b41f2afb4f548cdc5b97fffa0f26abe374715ba4ab6','REPORT.md':'2c00203f4cbe558ce827a25ce44da0edf134a68fefc1049f7ed377866e40af58'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    assert read(A/'ANCHORS.json')==anchors
    run=subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    assert run.stdout.strip()=='OK: 79 exact payloads; detached anchors; inventory/modes; read-only identity'
    m=read(A/'MANIFEST.json');assert m['schema']=='arithmetic152-exact-packet-v1'and len(m['files'])==79
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    objs=read(A/'private/source-bindings.json');assert len(objs)==12;folders=set();canonical=0;full_reads=0
    for x in objs:
        p=A/x['local'];d=p.read_bytes();e=lookup[x['path']];folders.add(x['path'].split('/build/')[0])
        assert p.resolve().is_relative_to(A.resolve())and len(d)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']and'/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'in x['url'];canonical+=1
        full_reads+=x['semantic_read_r2']==[0,x['size']]
    assert len(folders)==1 and full_reads==12
    closure=read(A/'private/include-closure.json');assert len(closure)==11 and all((A/'private/source'/x['resolved']).is_file()for x in closure)
    inputs=read(A/'private/input-bindings.json');completed=0;direct=0
    for x in inputs:
        p=P/x['path'];assert not p.is_symlink()
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert len(data)==x['end']-x['start']and hashlib.sha256(data).hexdigest()==x['sha256']and data==(A/x['copy']).read_bytes()
        if'/r150'in x['copy']:completed+=1
        else:direct+=1
    assert completed==6 and direct==4
    brief=B/'user-resume-2026-10-22-parent/arithmetic152-recovery-r2-brief.txt';assert sha(brief)=='ff8cbca852ddba122c0c3378f0ae215e18791f5daa5779ef97d8ccf190846ca8'and(A/'private/brief.txt').read_bytes()==brief.read_bytes()
    controls=read(A/'private/control-results.json');assert len(controls)==4 and sum(c['returncode']==0 for c in controls)==1 and controls[0]['name']=='good'
    prim=read(A/'private/primary-extents.json');pdfs=sorted(p.name for p in(A/'private/primary').glob('*.pdf'));assert len(pdfs)==11
    hist=read(A/'private/history-navigation.json')
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_members':79,'canonical_objects':canonical,'canonical_folders':1,'canonical_full_semantic_reads_declared':full_reads,'include_closure_edges':11,'canonical_matches_complete_pinned_tree':True,'direct_input_ranges':direct,'completed_exception_copies':completed,'selected_history_intervals':0,'history_navigation_note':'one guarded family-history navigation, no relevant admitted original; disclosed as a comparison limit, not clearance','primary_pdfs':len(pdfs),'primary_extent_records':len(prim)if isinstance(prim,list)else len(prim.keys()),'copied_controls':4,'authoritative_recovery_brief_copy_matches':True,'r1_root_was_empty':True,'entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, DERIVATIONS, PREFREEZE, UNRESOLVED, REPORT, RECOVERY, verify_packet.py and private/READING.md; parent rechecked the displayed finite arithmetic (b=301/302 crossover, Hodge-index endpoint bound, double-cover graph numbers, isotropic pairing). Source053 (12 TeX objects) and primary (Pixton2012, PPZ v3, PZ, Janda, EGL, Kong2026, OP Quot, Manolache, O Sullivan, Petersen, MOP) operative reading attributed to the child. No live Structural186/Arithmetic153 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_members','canonical_objects','include_closure_edges','direct_input_ranges','completed_exception_copies','primary_pdfs','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
