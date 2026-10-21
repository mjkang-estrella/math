#!/usr/bin/env python3
"""Read-only S183N contribution adoption; authentication is no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];R=B/'structural-r183-contribution-r1';A=B/'fresh-structural-discovery-r183'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
    anchors={'packet/FINAL.md':'be23da24ce6da12ad0fee3ca1015c2ca79981d52a74e0e7bb85c6f83fe38f331','packet/MANIFEST.json':'980a9143156acf964ea3fbcd00d6e381e73b24664cecb8eeea1c87b0a7c7eb98','REPORT.md':'f623ad63a07750360136ae291345a2193598a4d43a1cf16771ca64b242f07bcc'}
    before=snap(R);mode=stat.S_IMODE(R.stat().st_mode);author=snap(A);author_mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(R/n)==v for n,v in anchors.items())
    cmd=['python','-I','-B',str(R/'verify_packet.py'),'--packet',str(R/'packet'),'--report',str(R/'REPORT.md'),'--final-sha',anchors['packet/FINAL.md'],'--manifest-sha',anchors['packet/MANIFEST.json'],'--report-sha',anchors['REPORT.md'],'--check-inputs'];r=subprocess.run(cmd,cwd=P,text=True,capture_output=True,check=True);assert not r.stderr
    stable={};modes={};records=read(R/'private/unchanged-inputs-before.json');assert len(records)==47
    for x in records:
        p=P/x['path'];assert sha(p)==x['sha256']and p.stat().st_size==x['bytes']and stat.S_IMODE(p.stat().st_mode)==x['mode'];stable[x['path']]=x['sha256'];modes[x['path']]=x['mode']
    ranges=[]
    for x in read(R/'packet/private/author-metadata/history-extents.json'):
        with(P/x['path']).open('rb')as f:f.seek(x['start']);data=f.read(x['end']-x['start'])
        assert hashlib.sha256(data).hexdigest()==x['sha256'];ranges.append({'path':x['path'],'start':x['start'],'end':x['end'],'selection_sha256':x['sha256']})
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    bindings=read(R/'private/source-bindings.json');assert len(bindings)==12
    for x in bindings:
        p=R/x['review_copy'];data=p.read_bytes();e=lookup[x['path']];assert len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    manifest=read(R/'packet/MANIFEST.json');assert len(manifest['files'])==100
    for n in ['FINAL.md','REVIEW.md','READING-ISOLATION.md','verify_packet.py']:assert(R/n).read_bytes()==(R/'packet'/n).read_bytes()
    assert len(ranges)==3 and snap(R)==before and stat.S_IMODE(R.stat().st_mode)==mode and snap(A)==author and stat.S_IMODE(A.stat().st_mode)==author_mode;dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'artifact_only':True,'review_validator_stdout':r.stdout.strip(),'canonical_objects':12,'canonical_matches_complete_pinned_tree':True,'stable_named_originals':stable,'stable_original_modes':modes,'original_range_anchors':ranges,'explicit_original_records':47,'selected_history_intervals':3,'whole_i88_hash_not_supplied_or_invented':True,'entire_review_and_author_roots_unchanged':True,'wider_working_root_not_claimed_wholly_selected':True,'root_mode':mode,'payload_files':100,'parent_semantic_reading':'Complete REVIEW/FINAL/REPORT/READING-ISOLATION/verifier. REVIEW read in overlapping [0,15000) and [14500,end) displays with full union and no truncation. Actual source/primary/history reading is independently claimed by reviewer and remains attributed; parent authenticates bytes only. Initial whole acceptance-file binary overread, with only authorized slice decoded/displayed and no outside use, remains disclosed.'};dump(O/'replay.json',report);print(json.dumps({'payload_files':100,'canonical_objects':12,'original_records':47,'history_intervals':3,'author_review_unchanged':True,'artifact_only':True}))
if __name__=='__main__':main()
