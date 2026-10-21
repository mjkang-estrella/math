#!/usr/bin/env python3
"""Read-only Arithmetic146 intake; authentication assigns no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r146'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'FINAL.md':'f58e0234b4cbc22f48f153f009fd3832bd78a56dcad569c38e1bd6044062746e','MANIFEST.json':'91368c6c9575d6a0b22a8c05bac4d563f24cc6d4322141b4e9f3b27d34ed80c5','REPORT.md':'db0e1c4afdf9b33f947c33af3b0a5d0d2bd7b479d27c2dfc58a4fdf473bda115'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/n)==v for n,v in anchors.items())
    cmd=['python','-I','-B',str(A/'verify.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
    r=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(A/'private/source-bindings.json');assert len(bindings)==10
    for x in bindings:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert p.resolve().is_relative_to(A)and len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['blob']==e['sha']
    stable={};ranges=[];completed=0
    for x in read(A/'private/direct-extents.json'):
        start,end=x['extent']
        with(P/x['path']).open('rb')as f:f.seek(start);data=f.read(end-start)
        assert hashlib.sha256(data).hexdigest()==x['selected_sha256'];ranges.append({'path':x['path'],'start':start,'end':end,'selection_sha256':x['selected_sha256']})
        if x['path'].startswith('frontier/campaigns/'):
            p=P/x['path'];assert start==0 and end==p.stat().st_size;stable[x['path']]=x['selected_sha256'];completed+=1
    for x in read(A/'private/original-extents.json'):
        p=P/x['path'];assert sha(p)==x['original_sha256']and p.stat().st_size==x['original_bytes'];stable[x['path']]=x['original_sha256']
        with p.open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['selected_sha256']and data==(A/x['local']).read_bytes();ranges.append({'path':x['path'],'start':x['start'],'end':x['end'],'selection_sha256':x['selected_sha256']})
    assert completed==6 and len(stable)==11 and len(ranges)==16 and snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'author_validator_stdout':r.stdout.strip(),'canonical_objects':10,'canonical_matches_complete_pinned_tree':True,'stable_named_originals':stable,'original_range_anchors':ranges,'completed_originals':6,'selected_history_intervals':6,'distinct_original_history_bodies':5,'direct_instruction_ranges':4,'retrospective_direct_hashes_not_initial_final_comparisons':True,'entire_root_unchanged':True,'root_mode':mode,'payload_files':67,'outside_envelopes':3,'total_files':sum(v['kind']=='file'for v in before.values()),'parent_semantic_reading':'Complete PREFREEZE/DERIVATIONS/UNRESOLVED/FINAL/REPORT/private READING/selection-limits and verifier. DERIVATIONS read in overlapping [0,11000) and [10800,end) displays with full union and no truncation. Actual source/primary/history reading remains attributed to author; parent authenticates bytes only.'};assert report['total_files']==70;dump(O/'replay.json',report);print(json.dumps({'payload_files':67,'envelopes':3,'canonical_objects':10,'completed_originals':6,'history_intervals':6,'unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
