#!/usr/bin/env python3
"""Read-only Structural185 discovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r185'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'807f56f3a7228152d62290faf448e697d5ad4397466dc12d68a1fa28d16c2a59','private/MANIFEST.json':'bb05cd446315d0806a377f18302b2c598cc72660f9a7dbbc2ecdc745a7a80d4e','REPORT.md':'25de89f0d472986eb047da4d2a382deae11a11903c3445d4cd36c4f9f6d58fd4'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    detached=read(A/'ANCHORS.json');assert all(detached[k]['sha256']==anchors[detached[k]['path']] for k in('FINAL','MANIFEST','REPORT'))
    run=subprocess.run(['python','-I','-B',str(A/'VERIFY.py'),'packet','--root',str(A.relative_to(P)),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['private/MANIFEST.json'],'--report-sha',anchors['REPORT.md'],'--project-root',str(P)],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    out=json.loads(run.stdout);assert out['selected_files']==95 and out['source_blobs']==12 and out['exact_original_spans']==20
    m=read(A/'private/MANIFEST.json');assert len(m['entries'])==95
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    objs=read(A/'private/source-auth.json');assert len(objs)==12
    canonical=0
    for x in objs:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']]
        assert p.resolve().is_relative_to(A.resolve())and len(d)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['blob']==e['sha'];canonical+=1
    ranges=read(A/'private/history-extents.json');assert len(ranges)==10;stable={}
    for x in ranges:
        p=P/x['original'];assert not p.is_symlink()and p.stat().st_nlink==1
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert len(data)==x['end']-x['start']and hashlib.sha256(data).hexdigest()==x['sha256']and data==(P/x['copy']).read_bytes()
        if x['start']==0 and x['end']==p.stat().st_size:stable[x['original']]=x['sha256']
    completed=[A/f'private/completed177-{i}.txt'for i in range(6)];assert all(c.is_file()for c in completed)
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_validator_stdout':run.stdout.strip(),'payload_files':95,'canonical_objects':canonical,'canonical_matches_complete_pinned_tree':True,'selected_history_intervals':10,'whole_original_records':len(stable),'completed_exception_copies':6,'exact_original_spans_checked_by_author_verifier':20,'entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, DERIVATIONS, INTERFACES, COMPARISON and private/READING-LIMITS. Source309 and primary (Selick, Amelotte, Toda, Belmont-Shimomura, Carrick-Davies, partial MRW) operative reading attributed to the child, not fresh parent protected-body reading. No live Arithmetic151/Arithmetic152 bodies/findings/status/activity inspected or steered; both are user-paused interrupted records.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['payload_files','canonical_objects','selected_history_intervals','completed_exception_copies','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
