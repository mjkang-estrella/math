#!/usr/bin/env python3
"""Read-only Arithmetic153 discovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r153';K=A/'packet'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
def main():
    anchors={'packet/FINAL.md':'713756bf8e678a3c3f0fd7fa13b87e175d5b1fd1b4f7d80447fceeb413c463dc','MANIFEST.json':'8a07bc15810bc3ef1d4efed9b6cc6878ed5404d3f1c8a12c418422f141b2bb3a','REPORT.json':'7444d0826dda82703e2731e6c137ef5c20eb2e69320fa2e7f3227cb7a80a3b20'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    detached=read(A/'DETACHED-ANCHORS.json');assert {detached[k]['path']:detached[k]['sha256']for k in('FINAL','MANIFEST','REPORT')}==anchors
    run=subprocess.run(['python','-I','-B',str(K/'verify_packet.py'),'--packet',str(K),'--manifest',str(A/'MANIFEST.json'),'--report',str(A/'REPORT.json'),'--final-sha',anchors['packet/FINAL.md'],'--manifest-sha',anchors['MANIFEST.json'],'--report-sha',anchors['REPORT.json']],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    out=json.loads(run.stdout);assert out['artifact_status']=='MATCH'and out['packet_files']==63 and out['read_only']is True and out['mathematical_gate']is False
    m=read(A/'MANIFEST.json');assert m['schema']=='r153-exact-packet-v1'and len(m['files'])==63
    r=read(A/'REPORT.json');assert r['disposition']=='PREFREEZE/no nominee'and r['theorem_frozen']is False and r['packet_files']==63 and r['source_pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'and r['self_grades_assigned']is False and r['public_action']is False
    # every public packet member equals its root working copy; private trees are byte-identical
    public=[x['path']for x in m['files']if not x['path'].startswith('private/')];assert len(public)==10 and all((K/p).read_bytes()==(A/p).read_bytes()for p in public)
    priv=[x['path']for x in m['files']if x['path'].startswith('private/')];assert len(priv)==53 and all((K/p).read_bytes()==(A/p).read_bytes()for p in priv)
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    objs=read(K/'private/source-auth.json');assert len(objs)==11;canonical=0;folders=set()
    for x in objs:
        p=P/x['local'];d=p.read_bytes();e=lookup[x['path']];folders.add(x['path'].split('/')[1])
        assert p.resolve().is_relative_to(A.resolve())and len(d)==x['bytes']==e['size']and e['type']=='blob'and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];canonical+=1
    assert folders=={'Irrational-cubic-fourfolds-with-geometric-K3-categories-September-24-2026'}
    folder_blobs=[k for k,e in lookup.items()if k.startswith('preprints/Irrational-cubic-fourfolds-with-geometric-K3-categories-September-24-2026/')and e['type']=='blob'];assert sorted(folder_blobs)==sorted(x['path']for x in objs)
    edges=read(K/'private/include-edges.json');assert len(edges)==8 and all(e['from']=='paper.tex'for e in edges)
    sem=read(K/'private/semantic-extents.json');src=sem['source'];assert len(src)==11 and sum(s['semantic_read']for s in src)==10 and all(sha(K/s['path'])==s['sha256']and s['extent']==[0,(K/s['path']).stat().st_size]for s in src)
    ranges=read(K/'private/original-extents.json');assert len(ranges)==1 and ranges==sem['original_history']
    for x in ranges:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']==sha(K/'private/original-cross-family.txt')
    comp=sem['completed_direct_exceptions'];assert len(comp)==6
    for x in comp:
        o=B/x['original_relative_to_campaign'];d=o.read_bytes();assert x['extent']==[0,len(d)]and hashlib.sha256(d).hexdigest()==x['sha256']==sha(K/x['local'])and x['original_relative_to_campaign'].startswith(('discovery-arithmetic-r151-parent/','fresh-arithmetic-discovery-r151/'))
    prim=sem['primary'];assert len(prim)==8 and all(sha(K/x['path'])==x['sha256']and (K/x['path']).stat().st_size==x['bytes']and all(0<=a<b<=x['bytes']for a,b in x['semantic_byte_ranges'])for x in prim)
    assert sha(K/'private/acceptance.txt')==hashlib.sha256(span(P/'frontier/NEW-TEN-2026-10-14.md',4801,6347)).hexdigest()
    assert (K/'private/AGENTS.md').read_bytes()==(P/'AGENTS.md').read_bytes()and(K/'private/upstream.json').read_bytes()==(P/'sources/upstream.json').read_bytes()
    assert (K/'private/source054-catalogue.txt').read_bytes()==span(P/'sources/CONTENTS.md',94078,95390)
    brief=B/'expanded-target-2026-10-17/fresh-arithmetic-r153-brief.txt';assert sha(brief)=='3317dbfd42f7f32da40a96a451588a005919142e3eb260de268cdaed0732d75d'and brief.stat().st_size==22104
    controls=read(A/'controls-results.json');assert (A/'controls-results.json').read_bytes()==(K/'controls-results.json').read_bytes()and len(controls['controls'])==7 and all(c['exit_code']==c['expected_exit_code']and c['read_only_snapshot_unchanged']for c in controls['controls'])and sum(c['expected_exit_code']==0 for c in controls['controls'])==1 and sha(A/'controls-results.json')==r['artifact_controls']['results_sha256']
    fc=read(K/'private/finite-calculation.json');assert fc['d']==182 and fc['threshold_claim']is False and fc['roots_mod_d']==[19,33,149,163]and all((u*u+3)%364==0 for u in fc['roots_mod_d'])and sorted(map(sorted,fc['sign_orbits']))==[[19,163],[33,149]]
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':63,'public_packet_members_match_working_copies':len(public),'private_packet_members_match_working_copies':len(priv),'canonical_objects':canonical,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'include_edges':8,'source_text_objects_fully_read_by_child':10,'selected_history_intervals':1,'completed_exception_copies':6,'primary_extractions':8,'direct_inputs_matched':['AGENTS.md','sources/upstream.json','NEW-TEN[4801,6347)','CONTENTS[94078,95390)','brief sha'],'copied_controls':7,'finite_calculation_rechecked':'u^2=-3 mod 364 for 19,33,149,163; two sign orbits','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT.json, notes/00-03 and private/READING-ISOLATION.md. Source054 (10 text objects) and primary (KKPY v2, Lin-Shinder v2, Guere v2, Billi-Grossi-Marquand v2, Lin-Shinder-Zimmermann 2023, Fan-Lai 2023/2025, Bohning-von Bothmer-Marquand v2) operative reading attributed to the child, not fresh parent protected-body reading. Parent recomputed the d=182 gluing arithmetic (Gram det 182, N=<546>, |H|=182, four roots of u^2=-3 mod 364, two sign orbits, quotient q(z)=2/3) and the two-path incidence balance. No live Arithmetic154/Structural187 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','canonical_objects','selected_history_intervals','completed_exception_copies','primary_extractions','copied_controls','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
