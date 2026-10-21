#!/usr/bin/env python3
"""Read-only S183N correctness adoption; authentication is no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];R=B/'structural-r183-proof-r1';A=B/'fresh-structural-discovery-r183'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'packet/FINAL.md':'c0cfe4923114dd9dfc1b440aa37c2615d916cae4c0b8f549f7ae729efee4b51c','packet/MANIFEST.json':'52a39afe0d7b090d69aef7d2be7524ce4a894e8d4db98b44040ed4e6a5e8ee55','REPORT.md':'8e857ce7d1b122559a627b9d8e78a966b430f04feb2f40bf380aa7d032e82612'}
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);author=snap(A);author_mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(R/n)==v for n,v in anchors.items())
    cmd=['python','-I','-B',str(R/'verify_packet.py'),'--packet',str(R/'packet'),'--report',str(R/'REPORT.md'),'--final-sha',anchors['packet/FINAL.md'],'--manifest-sha',anchors['packet/MANIFEST.json'],'--report-sha',anchors['REPORT.md']];r=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    stable={};ranges=[];records=read(R/'private/authentication.json')['files'];assert len(records)==39
    for x in records:
        p=P/x['original'];q=R/x['copy']
        if 'range'in x:
            start,end=x['range']
            with p.open('rb')as f:f.seek(start);data=f.read(end-start)
            assert hashlib.sha256(data).hexdigest()==x['sha256']and data==q.read_bytes();ranges.append({'path':x['original'],'start':start,'end':end,'selection_sha256':x['sha256']})
        else:
            assert sha(p)==x['sha256']==sha(q)and p.stat().st_size==q.stat().st_size==x['bytes']and stat.S_IMODE(p.stat().st_mode)==stat.S_IMODE(q.stat().st_mode)==x['mode'];stable[x['original']]=x['sha256']
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(R/'private/author-private_source-bindings.json');assert len(bindings)==12
    for x in bindings:
        p=P/x['local'];data=p.read_bytes();e=lookup[x['path']];assert len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    manifest=read(R/'packet/MANIFEST.json');assert len(manifest['files'])==91
    for n in ['FINAL.md','REVIEW.md','READING-ISOLATION.md','verify_packet.py']:assert(R/n).read_bytes()==(R/'packet'/n).read_bytes()
    assert len(ranges)==3 and snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode and snap(A)==author and stat.S_IMODE(A.stat().st_mode)==author_mode;dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'review_validator_stdout':r.stdout.strip(),'canonical_objects':12,'canonical_matches_complete_pinned_tree':True,'stable_named_originals':stable,'original_range_anchors':ranges,'explicit_original_records':39,'whole_original_records':36,'selected_history_intervals':3,'whole_i88_hash_not_supplied_or_invented':True,'entire_review_and_author_roots_unchanged':True,'root_mode':mode,'payload_files':91,'parent_semantic_reading':'Complete REVIEW/FINAL/REPORT/READING-ISOLATION/verifier. REVIEW read in overlapping [0,14500) and [14000,end) displays with full union and no truncation. Actual source/primary/history reading is independently claimed by reviewer and remains attributed; parent authenticates bytes only.'};dump(O/'replay.json',report);print(json.dumps({'payload_files':91,'canonical_objects':12,'original_records':39,'whole_original_records':36,'history_intervals':3,'author_review_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
