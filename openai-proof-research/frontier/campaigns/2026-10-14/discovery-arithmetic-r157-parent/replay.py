#!/usr/bin/env python3
"""Read-only Arithmetic157 discovery intake; artifact checks only, no mathematical gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess
from fractions import Fraction as Fr
from math import asin,pi,sqrt
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r157';K=A/'packet';V=K/'private'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
def main():
    anchors={'FINAL_SHA256':'3584b82a7a831a3f745ce6ce408a04ae1bd7912837fa65576c7d475694339c06','MANIFEST_SHA256':'6b4b5d627feeed0bb16a2b18b901f1472ef3e12ee6f3765f82f15f8f8b8421f3','REPORT_SHA256':'50b7019c50eb0e81212fbed4be3046521a017acc5bd288b7e0daf08d47432b6b'}
    F,M,R=anchors['FINAL_SHA256'],anchors['MANIFEST_SHA256'],anchors['REPORT_SHA256']
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode)
    assert sha(K/'FINAL.md')==F and sha(A/'MANIFEST.json')==M and sha(A/'REPORT.json')==R and read(A/'DETACHED-ANCHORS.json')==anchors
    run=subprocess.run(['python','-I','-B',str(K/'verify_packet.py'),str(A),'--final-sha256',F,'--manifest-sha256',M,'--report-sha256',R],cwd=P,capture_output=True,text=True,check=True)
    assert not run.stderr and run.stdout.strip()=='MATCH: 87 packet files, 6744169 bytes; artifact integrity only'==(A/'VERIFY.txt').read_text().strip()
    m=read(A/'MANIFEST.json');assert m['schema']=='r157-exact-selected-packet-v1'and len(m['files'])==87 and sum(x['bytes']for x in m['files'])==6744169;names={x['path']for x in m['files']}
    assert {'FINAL.md','notes/00-feasibility-checkpoint.md','notes/01-operative-comparison.md','notes/02-integrated-scaling-reduction.md','notes/03-admissible-returns-and-unpaid-operation.md','verify_packet.py','private/READING-ISOLATION.md'}<=names
    rep=read(A/'REPORT.json');assert rep['disposition']=='PREFREEZE / no nominee'and rep['theorem_frozen']is False and rep['final_sha256']==F and rep['manifest_sha256']==M and rep['source_blobs_authenticated']==23 and rep['source_text_blobs_fully_read']==14 and rep['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    rootfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};assert len(rootfiles)==95 and rootfiles=={'packet/'+n for n in names}|{'MANIFEST.json','REPORT.json','DETACHED-ANCHORS.json','VERIFY.txt','record_coverage.py','seal_selected.py','select_authored.py','select_authored_secondary.py'}
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    auth=read(V/'authentication.json');assert len(auth)==23;folders=set()
    for x in auth:
        e=lookup[x['path']];p=V/'upstream'/x['path'];d=p.read_bytes();folders.add(x['path'].split('/')[1])
        assert e['type']=='blob'and len(d)==x['size']==e['size']and sha(p)==x['sha256']and hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==x['sha']==e['sha']and x['url_raw']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert len(folders)==2 and sorted(k for k,e in lookup.items()if e['type']=='blob'and k.split('/')[1]in folders and k.startswith('preprints/'))==sorted(x['path']for x in auth)
    sel=read(V/'selected-tree.json');assert len(sel)==28 and sorted(x['path']for x in sel if x['type']=='blob')==sorted(x['path']for x in auth)and all(lookup[x['path']]['sha']==x['sha']for x in sel)
    wrappers={'preprints/Semialgebraic-universal-covers-of-normal-projective-varieties-September-24-2026/build/main.tex':('145b8ff0dfe897edcd6754493a085494eef1bcc2',18083),'preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/build/paper.tex':('75578580f59258c45f53aafb6b8345ca2e354f11',11534)}
    assert all(lookup[k]['sha']==v[0]and lookup[k]['size']==v[1]for k,v in wrappers.items())
    cov=read(V/'source-coverage.json');assert len(cov)==23;cnt={}
    for x in cov:
        cnt[x['status']]=cnt.get(x['status'],0)+1;assert x['bytes']==lookup[x['path']]['size']and x['sha256']==sha(V/'upstream'/x['path'])
        if x['status']=='complete semantic read':assert x['read_intervals']==[[0,x['bytes']]]and x['unread_intervals']==[]
        else:assert x['read_intervals']==[]and x['unread_intervals']==[[0,x['bytes']]]
    assert cnt=={'complete semantic read':14,'authenticated only':9}
    edges=read(V/'include-edges.json');assert len(edges)==17 and all(e['from']in lookup for e in edges)
    brief=V/'authoritative-brief.txt';assert brief.read_bytes()==(B/'expanded-target-2026-10-17/fresh-arithmetic-r157-brief.txt').read_bytes()and sha(brief)=='bfafc9e8a536da3c7c61ff35274fa20ac3b17e2a52817db0887856265aa35999'and brief.stat().st_size==25517
    assert (V/'AGENTS.md').read_bytes()==(P/'AGENTS.md').read_bytes()and (V/'upstream.json').read_bytes()==(P/'sources/upstream.json').read_bytes()and (V/'acceptance-4801-6347.txt').read_bytes()==span(P/'frontier/NEW-TEN-2026-10-14.md',4801,6347)
    ce=read(V/'completed-extents.json');assert len(ce)==6
    for x in ce:
        o=P/x['path'];assert'r155'in x['path']and x['read_intervals']==[[0,o.stat().st_size]]and sha(o)==x['sha256']==sha(V/x['copy'])and (V/x['copy']).read_bytes()==o.read_bytes()
    hx=read(V/'history-extents.json');assert len(hx)==4
    for x in hx:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and (V/x['copy']).read_bytes()==d
    nav=read(V/'history-navigation.json');nav2=read(V/'history-secondary-navigation.json');assert nav['eligible_utf8']==nav2['eligible_utf8']==1714 and nav['nonutf8']==nav2['nonutf8']==12
    pe=read(V/'primary-extents.json');ac=read(V/'primary/access.json');assert len(pe)==5 and len(ac)==5;pr={}
    for x in ac:assert sha(V/'primary'/(x['name']+'.pdf'))==x['sha256']and (V/'primary'/(x['name']+'.pdf')).stat().st_size==x['bytes']
    for x in pe:
        t=V/'primary'/(x['name']+'.txt');assert t.stat().st_size==x['text_bytes']and sha(t)==x['text_sha256'];pr[x['name']]=x['read_intervals']
    assert pr['Vey1970']==[[0,59795]]and pr['KPv2']==[[0,53984]]and pr['Piecewise2026']==[[0,41718]]and pr['LiuWu']==[[0,27000],[28240,43000],[77208,108305]]and pr['Zimmer2021']==[]
    vc=read(V/'primary/version-confirmation.json');assert [(x['name'],x['matches_initial_download'])for x in vc]==[('LiuWu',True),('Piecewise2026',True)]and {x['name']:x['sha256']for x in vc}=={x['name']:x['sha256']for x in ac if x['name']in('LiuWu','Piecewise2026')}
    ctl=read(V/'controls-results.json');assert [(c['control'],c['exit_code'],c['expected_match'])for c in ctl]==[('golden',0,True),('changed',1,False),('missing',1,False),('extra',1,False)]
    g=read(V/'guards.json');assert len(g['wildcards'])==150 and len(g['substrings'])==150 and g['own_root']=='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r157'and '*arithmetic*r156*'in g['wildcards']and '*structural*r189*'in g['wildcards']and 'publication'in g['substrings']
    # Parent finite rechecks of Note 03 (artifact of the author's test calculations, not a mathematical gate)
    assert abs(2*asin(0.5)-pi/3)<1e-12                                   # modular fundamental-region area pi/3
    for c,d in[(1,0),(1,1),(2,1),(3,2),(0,1)]:                           # Im(gamma i)=1/(c^2+d^2)<=1
        assert Fr(1,c*c+d*d)<=1
    for j in(10,100,1000):                                              # Cayley rates (6)
        z=complex(j,1);zeta=(z-1j)/(z+1j);assert abs(zeta-j/(j+2j))<1e-12 and abs(abs(1-zeta)-2/sqrt(j*j+4))<1e-12 and abs((1-abs(zeta))*j*j/2-1)<4/(j*j)
    for e in(Fr(1,10),Fr(1,1000)):                                      # two-rate quadrant: ratio independent of t
        v=(e,e*e);assert all((v[1]/t)/(v[0]/t)==e for t in(e,e*e,Fr(1,7)))
    assert Fr(3,2)-2==Fr(-1,2)                                          # t^(3/2)/t^2=t^(-1/2) exponent bookkeeping
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':87,'packet_bytes':6744169,'root_files':95,'exterior_files':8,'canonical_objects':23,'canonical_folders':2,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'wrapper_anchors':2,'source_coverage':cnt,'include_edges':17,'completed_exception_copies':6,'history_extents':4,'history_eligible_utf8':1714,'primary_pdfs':5,'primary_fully_read':['Vey1970','KPv2','Piecewise2026'],'primary_partially_read':['LiuWu'],'primary_not_read':['Zimmer2021'],'copied_controls':4,'parent_exact_rechecks':'modular fundamental-region area 2*asin(1/2)=pi/3; Im(gamma i)=1/(c^2+d^2)<=1; Cayley rates |1-zeta_j|=2/sqrt(j^2+4) and 1-|zeta_j|~2/j^2; two-rate quadrant ratio epsilon_j independent of scalar t_j; t^(3/2)/t^2=t^(-1/2)','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT.json, DETACHED-ANCHORS, VERIFY.txt, verify_packet.py, note 03 in large part, and private/READING-ISOLATION.md in large part; notes 00-02 openings. Source058 (14 complete text objects of two folders; six long classification sections, bibliography and two PDFs authenticated only) and primary (Vey 1970, Kollar-Pardon v2, Pu-Wang v1 complete; Kuai-Liu-Wu v3 operative units; Zimmer 2021 not read) reading attributed to the child, not fresh parent protected-body reading. No live Structural189 or Arithmetic156 review bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','canonical_objects','completed_exception_copies','history_extents','primary_pdfs','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
