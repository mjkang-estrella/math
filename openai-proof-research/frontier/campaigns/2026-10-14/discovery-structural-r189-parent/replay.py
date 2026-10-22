#!/usr/bin/env python3
"""Read-only Structural189 discovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r189';V=A/'private'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
def monomial_ranks(L,N,K):
    # D_L=[R --x^L--> R], R=k[[x]], truncated at level K then mapped to level N<=K; monomial bases make the ranks exact
    ker_K={i for i in range(K)if i+L>=K}                       # H^0 at level K: monomials x^i with x^{i+L}=0 mod x^K
    h0_image=len({i for i in ker_K if i<N})                   # image of H^0(level K) in H^0(level N)
    h1_K=min(K,L);h1_N=min(N,L);h1_image=min(h1_K,h1_N)       # H^1=k[x]/(x^K,x^L) -> k[x]/(x^N,x^L), surjective
    return h0_image,h1_image
def main():
    anchors={'FINAL.md':'94444892974c68c527365579b9129bb5f3e3cc2f1a8c90f7a24ea5733ec888ff','MANIFEST.json':'1e290d6a897dc76adf12950ee8abc54b1289f1f4306f9949c0f51b09613cb1f7','REPORT.md':'72f4e9f20a0d0ae88d8a6aa9ba8aa917bd301b81cb258ed409a619fbbc5ff223'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    ac=read(A/'ANCHORS.json');assert ac['algorithm']=='SHA256'and ac['anchors']==anchors
    run=subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    assert json.loads(run.stdout)=={'artifact_verification':'matched','selected_files':74}
    st=read(A/'SEAL-TESTS.json');assert st['exit_code']==0 and json.loads(st['stdout'])=={'artifact_verification':'matched','selected_files':74}and st['anchor_bytes_unchanged_after_verification']is True and st['controls_results_sha256']==sha(V/'controls/control-results.json')
    m=read(A/'MANIFEST.json');assert m['format']=='r189-exact-packet-v1'and len(m['files'])==74 and sum(x['bytes']for x in m['files'])==7297955
    names={x['path']for x in m['files']};assert {'DERIVATIONS.md','INTERFACES.md','COMPARISON.md','verify_packet.py','private/READING-LIMITS.md'}<=names and 'FINAL.md'not in names and not any(n.startswith('private/controls/')for n in names)
    for x in m['files']:assert (A/x['path']).stat().st_size==x['bytes']and sha(A/x['path'])==x['sha256']
    allfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};ctrl={f for f in allfiles if f.startswith('private/controls/')}
    assert allfiles-ctrl==names|{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json','SEAL-TESTS.json'}and len(allfiles)==100
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    folder='preprints/Finite-generation-for-the-Kn-local-sphere-September-24-2026/'
    sa=read(V/'source-authentication.json');assert len(sa)==19
    for x in sa:
        p=V/'source'/x['path'];d=p.read_bytes();e=lookup[x['path']]
        assert x['path'].startswith(folder)and len(d)==x['bytes']==e['size']and e['type']=='blob'and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['git_blob']==e['sha']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert sorted(k for k,e in lookup.items()if k.startswith(folder)and e['type']=='blob')==sorted(x['path']for x in sa)
    ft=read(V/'family-tree.json');assert len(ft)==24 and sorted(x['path']for x in ft if x['type']=='blob')==sorted(x['path']for x in sa)and all(lookup[x['path']]['sha']==x['sha']for x in ft)
    wrap=[x for x in sa if x['path']==folder+'build/main.tex'][0];assert wrap['bytes']==1682 and wrap['git_blob']=='5a7c121c435beec612435ca0340bc217c7f92225'
    sre=read(V/'source-reading-extents.json');assert len(sre)==19 and sum(1 for x in sre if x['semantic_read'])==18
    for x in sre:assert x['start']==0 and x['end']==lookup[x['path']]['size']and x['sha256']==sha(V/'source'/x['path'])
    assert [x['path']for x in sre if not x['semantic_read']]==[folder+'Finite-generation-for-the-Kn-local-sphere-September-24-2026.pdf']
    dr=read(V/'direct-reads.json');assert len(dr)==13
    for x in dr:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and (A/x['copy']).read_bytes()==d
    comp=[x for x in dr if 'r188'in x['path']or'r187'in x['path']];assert len(comp)==10 and all(x['start']==0 and x['end']==(P/x['path']).stat().st_size for x in comp)
    nt=[x for x in dr if x['path']=='frontier/NEW-TEN-2026-10-14.md'][0];assert (nt['start'],nt['end'])==(4801,6347)
    assert not any(x['path']=='sources/CONTENTS.md'for x in dr)and {x['path']for x in dr}>={'AGENTS.md','sources/upstream.json'}
    brief=V/'authoritative-brief.txt';assert brief.read_bytes()==(B/'expanded-target-2026-10-17/fresh-structural-r189-brief.txt').read_bytes()and sha(brief)=='24316da51ff1e807174785b9106b2d3999ac5cdf90b48671ccb9972dd276cd66'and brief.stat().st_size==24878
    hx=read(V/'history-extents.json');hl=read(V/'history-late-extents.json');assert len(hx)==9 and len(hl)==2
    for x in hx+hl:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and (A/x['copy']).read_bytes()==d
        assert not any(t in x['path']for t in('r189','r188','r187','r156','r157','structural-discovery-r18','arithmetic-discovery-r15'))
    hn=read(V/'history-navigation.json');assert hn['eligible_files_read_for_selection']==1726 and hn['nonutf8']==12 and len(hn['hits'])==298
    acq=read(V/'primary/acquisition.json');pr=read(V/'primary-reading-extents.json');assert len(acq)==6 and len(pr)==6;pages={}
    for x in acq:assert sha(V/'primary'/(x['name']+'.pdf'))==x['sha256']and (V/'primary'/(x['name']+'.pdf')).stat().st_size==x['bytes']
    for x in pr:
        t=(V/'primary'/(x['name']+'.txt')).read_bytes();assert hashlib.sha256(t).hexdigest()==x['extracted_text_sha256']
        assert sorted(e['page']for e in x['extents'])==sorted(x['semantic_read_pages'])and all(0<=e['start']<e['end']<=len(t)for e in x['extents']);pages[x['name']]=len(x['semantic_read_pages'])
    assert pages=={'bssw':10,'li':16,'heard':4,'hs':7,'bb':9,'dh':12}and sum(pages.values())==58
    cr=read(V/'controls/control-results.json');assert [(r['case'],r['expected_exit'],r['actual_exit'])for r in cr['results']]==[('good',0,0),('payload-tamper',1,1),('final-tamper',1,1),('manifest-tamper',1,1),('report-tamper',1,1)]and cr['original_synthetic_anchors_unchanged']is True
    g=read(V/'guards.json');assert len(g['wildcards'])==150 and len(g['substrings'])==150 and g['own_root']=='frontier/campaigns/2026-10-14/fresh-structural-discovery-r189'and {'*arithmetic*r156*','*arithmetic*r157*'}<=set(g['wildcards'])and 'publication'in g['substrings']
    # Parent independent recheck of the finite-matrix control (DERIVATIONS section 8): exact monomial-basis ranks for D_L=[R --x^L--> R]
    fm=read(V/'finite-matrix-control.json');assert len(fm['rows'])==48
    for r in fm['rows']:
        L,N,K=r['L'],r['N'],r['K'];assert K>=N
        h0,h1=monomial_ranks(L,N,K);assert (h0,h1)==(r['H0_image_rank'],r['H1_image_rank'])==(max(0,N-max(K-L,0)),min(N,L))
    for L in(3,6):
        for N in range(1,9):assert monomial_ranks(L,N,N+L)[0]==0 and monomial_ranks(L,N,N+L-1)[0]==min(N,1)and monomial_ranks(L,N,N+L)[1]==min(N,L)  # b(N)=N+L is the first level with zero H^0 image
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'seal_tests_match':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':74,'packet_bytes':7297955,'root_files':100,'control_files':len(ctrl),'canonical_objects':19,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'wrapper_anchor':{'path':folder+'build/main.tex','bytes':1682,'git_blob':'5a7c121c435beec612435ca0340bc217c7f92225'},'source_text_objects_fully_read':18,'source_pdf_authenticated_only':1,'direct_reads':13,'completed_exception_copies':10,'history_sections':11,'history_late_sections':2,'history_eligible_files':1726,'primary_pdfs':6,'primary_pages':58,'copied_controls':5,'finite_matrix_rows_rechecked':48,'parent_exact_rechecks':'exact monomial-basis image ranks of D_L=[R --x^L--> R] from level K to level N<=K equal max(0,N-max(K-L,0)) on H^0 and min(N,L) on H^1 for all 48 recorded rows; H^0 image first vanishes at K=N+L, so b(N)=N+L','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, ANCHORS, SEAL-TESTS, verify_packet.py, DERIVATIONS section 8 and openings of DERIVATIONS, INTERFACES, COMPARISON and private/READING-LIMITS. Source313 (eighteen text objects) and primary (six acquired PDFs, 58 pages) operative reading attributed to the child, not fresh parent protected-body reading. No live Arithmetic156 review bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','canonical_objects','direct_reads','history_sections','primary_pages','finite_matrix_rows_rechecked','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
