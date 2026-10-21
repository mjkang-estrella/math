#!/usr/bin/env python3
"""Read-only S182P correctness-review intake; artifacts do not prove mathematics."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2];ROOT=B/'structural-r182-proof-r1'
sp=importlib.util.spec_from_file_location('snapshot',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def main():
    anchors={'FINAL.json':'49ef63081efa7594630f5b8c16f5a53943e207367dca66f833e5b2710a41b046','packet/MANIFEST.json':'85852ea1e8856139d5ab8f38dee536f25c693163bfcd0855c548ea72a5b797da','REPORT.md':'938e3a2ad825db2d271a3466b0edd03501d5598c51ab6001f38a8bc5220e725a'}
    before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);assert all(sha(ROOT/p)==v for p,v in anchors.items())
    r=subprocess.run(['python','-I','-B',str(ROOT/'packet/verify_packet.py'),'--root',str(ROOT),'--final-sha256',anchors['FINAL.json'],'--manifest-sha256',anchors['packet/MANIFEST.json'],'--report-sha256',anchors['REPORT.md'],'--originals','--project',str(P)],cwd=P,text=True,capture_output=True,check=True);assert not r.stderr and json.loads(r.stdout)=={'artifact_verification':'PASS','packet_members':48,'original_anchors_checked':35,'mathematical_gate':False}
    m=read(ROOT/'packet/MANIFEST.json');assert len(m['members'])==48;names={x['path']for x in m['members']};assert {p.removeprefix('packet/')for p,x in before.items()if x['kind']=='file'and p.startswith('packet/')and p!='packet/MANIFEST.json'}==names
    for x in m['members']:
        p=ROOT/'packet'/x['path'];assert stat.S_IMODE(p.stat().st_mode)==x['mode']
    tree=read(P/'sources/preprints-tree.json');lookup={x['path']:x for x in tree['tree']};assert not tree['truncated']and len(lookup)==13223 and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';canonical=[x for x in read(ROOT/'packet/private/copy-authentication.json')if 'canonical_path'in x];assert len(canonical)==2
    for x in canonical:
        p=ROOT/'packet'/x['copy'];data=p.read_bytes();e=lookup[x['canonical_path']];assert len(data)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob']==e['sha']
    stable={};ranges=[];originals=read(ROOT/'packet/private/original-anchors.json');assert len(originals)==35;copies=0
    for x in originals:
        p=P/x['original']
        if 'range'in x:
            a,b=x['range']
            with p.open('rb')as f:f.seek(a);data=f.read(b-a)
            ranges.append({'path':x['original'],'start':a,'end':b,'selection_sha256':x['sha256']})
        else:data=p.read_bytes();stable[x['original']]=x['sha256']
        assert len(data)==x['bytes']and hashlib.sha256(data).hexdigest()==x['sha256']and stat.S_IMODE(p.stat().st_mode)==x['mode']
        if 'copy'in x:assert data==(ROOT/'packet'/x['copy']).read_bytes();copies+=1
    f=read(ROOT/'FINAL.json');assert f['verdict']=='PASS'and f['unchanged_author_proof_established']and not f['necessary_author_corrections']and not f['unresolved_correctness_objections']and not f['essential_uncompleted_correctness_verifications']and sha(ROOT/'packet/REVIEW.md')==f['review_sha256']
    author=B/'fresh-structural-discovery-r182';obs=read(B/'discovery-structural-r182-parent/observed-root.json');assert snap(author)==obs['root']and stat.S_IMODE(author.stat().st_mode)==obs['root_mode']and sha(author/'FROZEN-THEOREM.md')==f['frozen_statement_sha256']and sha(author/'notes/03-author-proof.md')==f['author_proof_sha256']
    assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode
    (O/'observed-root.json').write_text(json.dumps({'root':before,'root_mode':mode},indent=2)+'\n');result={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'author_verifier_stdout':r.stdout.strip(),'parent_exact_packet_membership_and_modes_checked':True,'payload_files':48,'canonical_objects':2,'explicit_original_anchors':35,'matched_original_copies':copies,'stable_named_originals':stable,'original_range_anchors':ranges,'frozen_scope_sha256':f['frozen_statement_sha256'],'author_proof_sha256':f['author_proof_sha256'],'review_sha256':f['review_sha256'],'entire_review_root_and_author_root_unchanged':True,'artifact_only':True,'parent_semantic_reading':'Complete REVIEW, FINAL, REPORT, reading-and-isolation, verifier. A124-token combined-output truncation in REVIEW section8 was recovered by a separate byte17000-to-EOF display. Actual source/primary semantic extents remain attributed to independent reviewer.'};(O/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['payload_files','canonical_objects','explicit_original_anchors','matched_original_copies','entire_review_root_and_author_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
