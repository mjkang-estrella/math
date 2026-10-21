#!/usr/bin/env python3
"""Read-only S182P contribution-review intake; artifacts are not mathematical gates."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];ROOT=B/'structural-r182-contribution-r1'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.json':'9c4f33902e859bc20ec1429d5de741caf995a603fc5b1c0b305b54950e3c9424','packet/MANIFEST.json':'077b9ab3d18102e9da6a8140db1291d76441694b304f5445edd2363cc28d5b74','REPORT.md':'e5de5c96e3f7a44dd4cc0ae9b09ee8f75de91f91bbd9c72177274eac86374f53'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'packet/verify_packet.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.json'],'--manifest-sha256',anchors['packet/MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--check-originals'],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr and json.loads(r.stdout)=={'artifact_verification':'MATCH','members':40,'explicit_originals_checked':True,'mathematical_gate':False}
    m=read(ROOT/'packet/MANIFEST.json');assert len(m['members'])==40;names={x['path']for x in m['members']};assert {p.removeprefix('packet/')for p,x in before.items()if x['kind']=='file'and p.startswith('packet/')and p!='packet/MANIFEST.json'}==names
    for name in ['REVIEW.md','READING-ISOLATION.md']:assert(ROOT/name).read_bytes()==(ROOT/'packet'/name).read_bytes()
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';canonical=read(ROOT/'packet/private/own-source-authentication.json')['source_objects'];assert len(canonical)==2
    for x in canonical:
        p=ROOT/'packet/private'/Path(x['path']).name;data=p.read_bytes();e=lookup[x['path']];assert len(data)==x['bytes']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    stable={};originals=read(ROOT/'packet/private/original-anchors.json');assert len(originals)==2
    for x in originals:assert sha(P/x['path'])==x['sha256']and stat.S_IMODE((P/x['path']).stat().st_mode)==x['mode'];stable[x['path']]=x['sha256']
    bindings=read(ROOT/'packet/private/bindings.json');assert len(bindings)==7
    for x in bindings:
        p=P/x['original'];copy=ROOT/'private'/x['copy'];assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']and p.read_bytes()==copy.read_bytes();stable[x['original']]=x['sha256']
    ranges=[]
    for x in read(ROOT/'packet/private/history-reads.json'):
        a,b=x['extent'];p=P/x['path']
        with p.open('rb')as f:f.seek(a);data=f.read(b-a)
        assert hashlib.sha256(data).hexdigest()==x['sha256']and data==(ROOT/'packet/private'/x['copy']).read_bytes();ranges.append({'path':x['path'],'start':a,'end':b,'selection_sha256':x['sha256']})
    excerpts=read(ROOT/'packet/private/selected-excerpts.json');assert len(excerpts)==4
    for x in excerpts:
        a,b=x['original_range'];p=ROOT/'private'/x['working_body']
        with p.open('rb')as f:f.seek(a);data=f.read(b-a)
        assert len(data)==x['bytes']and hashlib.sha256(data).hexdigest()==x['sha256']and data==(ROOT/'packet'/x['selected_file']).read_bytes()
    f=read(ROOT/'FINAL.json');assert f['contribution_verdict']=='TECHNICAL'and f['correctness_grade']is None and f['acceptance']is None and f['count']is None and f['unpaid_contribution_integration_obligation']is None and f['peer_review_blind']
    author=B/'fresh-structural-discovery-r182';obs=read(B/'discovery-structural-r182-parent/observed-root.json');assert snap(author)==obs['root']and stat.S_IMODE(author.stat().st_mode)==obs['root_mode']and sha(author/'FROZEN-THEOREM.md')==f['frozen_sha256']and sha(author/'notes/03-author-proof.md')==f['author_proof_sha256']
    assert len(ranges)==3 and len(stable)==9 and snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'reviewer_verifier_stdout':r.stdout.strip(),'parent_exact_packet_membership_checked':True,'payload_files':40,'canonical_objects':2,'explicit_author_anchors':2,'bound_original_bodies':7,'selected_original_sections':3,'selected_primary_excerpts':4,'stable_named_originals':stable,'original_range_anchors':ranges,'frozen_scope_sha256':f['frozen_sha256'],'author_proof_sha256':f['author_proof_sha256'],'review_sha256':sha(ROOT/'REVIEW.md'),'entire_review_root_and_author_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete REVIEW, FINAL, REPORT, READING-ISOLATION and verifier. Actual source/primary semantic extents attributed to independent reviewer. CL access limit and initial whole-file byte load with only acceptance-window decoding/use are retained.'};(O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['payload_files','canonical_objects','explicit_author_anchors','bound_original_bodies','selected_original_sections','entire_review_root_and_author_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
