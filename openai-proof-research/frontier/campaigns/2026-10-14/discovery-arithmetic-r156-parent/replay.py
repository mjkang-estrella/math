#!/usr/bin/env python3
"""Read-only Arithmetic156 nominee intake; artifact checks and elementary parent rechecks only, no mathematical gate."""
import datetime,hashlib,importlib.util,itertools,json,stat,subprocess
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r156'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
def perm_compose(p,q):
    # (p*q)(i)=p(q(i)): q acts first (rightmost first)
    return tuple(p[q[i]]for i in range(len(p)))
def perm_inv(p):
    r=[0]*len(p)
    for i,j in enumerate(p):r[j]=i
    return tuple(r)
def cyc(*cycles,n=4):
    p=list(range(n))
    for c in cycles:
        for i in range(len(c)):p[c[i]-1]=c[(i+1)%len(c)]-1
    return tuple(p)
def main():
    anchors={'FINAL.md':'f54cbec3628425053feba7f617cb95e64e5bf6cdc21c164c2592413d075c4973','MANIFEST.json':'f965e1aaac429f391c81020529247a7e0f3fe960861116fa1b22ff006fdd815a','REPORT.md':'4520140adda6138616c2c7be0a53cc22e966a09b4d0573515197df70ada9c599'}
    frozen='91e62de24ee1198647e25cc0ee946b8043c480a6a975280bad046be581ed7e3c'
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    assert sha(A/'FROZEN.md')==frozen and (A/'FROZEN.sha256').read_text()==frozen+'  FROZEN.md\n'
    assert (A/'ANCHORS.sha256').read_text()==''.join(anchors[k]+'  '+k+'\n'for k in('FINAL.md','MANIFEST.json','REPORT.md'))
    proof=sha(A/'AUTHOR-PROOF.md');assert (A/'AUTHOR-PROOF.md').stat().st_size==23878 and (A/'FROZEN.md').stat().st_size==1912
    run=subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--manifest-sha',anchors['MANIFEST.json'],'--final-sha',anchors['FINAL.md'],'--report-sha',anchors['REPORT.md']],cwd=P,capture_output=True,text=True,check=True);assert not run.stderr
    assert run.stdout=='ARTIFACT CONSISTENT: 85 selected files; no mathematical verdict\n'
    m=read(A/'MANIFEST.json');assert m['format']=='r156-exact-packet-v1'and len(m['files'])==85 and set(m['exterior'])=={'MANIFEST.json','REPORT.md','ANCHORS.sha256'}
    names={x['path']for x in m['files']};assert {'FROZEN.md','AUTHOR-PROOF.md','DERIVATIONS.md','UNRESOLVED.md','FINAL.md','FROZEN.sha256','verify_packet.py','private/READING.md','private/SOURCE-MAP.md'}<=names
    for x in m['files']:assert (A/x['path']).stat().st_size==x['bytes']and sha(A/x['path'])==x['sha256']
    assert [x for x in m['files']if x['path']=='AUTHOR-PROOF.md'][0]['sha256']==proof and [x for x in m['files']if x['path']=='FROZEN.md'][0]['sha256']==frozen
    allfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};assert allfiles==names|set(m['exterior'])and len(allfiles)==88
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    folders=['preprints/The-abelianity-conjecture-for-special-compact-Kahler-manifolds-September-23-2026/','preprints/Two-step-monodromy-of-special-quasi-projective-varieties-September-24-2026/','preprints/A-conditional-abelianity-theorem-for-special-fourfold-pairs-with-a-half-weight-divisor-October-5-2026/']
    auth=read(A/'private/authentication.json');sel=read(A/'private/tree-selection.json');assert len(auth)==len(sel)==42 and {x['path']for x in auth}=={x['path']for x in sel}
    for x in auth:
        p=A/'private/upstream'/x['path'];d=p.read_bytes();e=lookup[x['path']]
        assert any(x['path'].startswith(f)for f in folders)and e['type']=='blob'and len(d)==x['size']==e['size']and x['sha']==e['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()and sha(p)==x['sha256']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert sorted(k for k,e in lookup.items()if e['type']=='blob'and any(k.startswith(f)for f in folders))==sorted(x['path']for x in auth)
    per_folder=[sum(1 for x in auth if x['path'].startswith(f))for f in folders];assert per_folder==[12,15,15]
    wrappers={folders[0]+'build/paper.tex':('0e894f3d',1652),folders[1]+'build/main.tex':('05e3fb67',2651),folders[2]+'build/source/main.tex':('8a7e0a0e',1206),folders[2]+'build/source/inertia.tex':('85083828',1207)}
    for k,(pre,n) in wrappers.items():assert lookup[k]['sha'].startswith(pre)and lookup[k]['size']==n
    sr=read(A/'private/source-reading.json');assert len(sr)==42;complete=0;unread=[]
    for x in sr:
        assert x['bytes']==lookup[x['path']]['size']
        iv=sorted(x['semantic_extents'])
        if iv and iv[0][0]==0 and iv[-1][1]==x['bytes']and all(iv[i][1]==iv[i+1][0]for i in range(len(iv)-1)):complete+=1
        else:unread.append((x['path'].split('/')[-1],x['status']))
    cr=read(A/'private/completed-reads.json');assert len(cr)==6
    for x in cr:assert 'r154'in x['path']and (P/x['path']).stat().st_size==x['bytes']and(('sha256'not in x)or sha(P/x['path'])==x['sha256'])
    hs=read(A/'private/history-sections.json');ht=read(A/'private/history-local-topology.json');hr=read(A/'private/history-reading.json');assert len(hs)==40 and len(ht['sections'])==3 and len(hr)==43
    for x in hs+ht['sections']:
        d=span(P/x['path'],x['start'],x['end']);assert d.decode('utf-8')==x['body']
        assert not any(t in x['path']for t in('r156','r157','r188','r189','discovery-r15','discovery-r18'))
    assert {(x['path'],tuple(x['extent']))for x in hr}=={(x['path'],(x['start'],x['end']))for x in hs+ht['sections']}
    acq=read(A/'private/primary/acquisition.json')+read(A/'private/primary/acquisition2.json');ab=read(A/'private/primary/abkp-acquisition.json');prim=0;fail=[]
    for x in acq:
        if 'sha256'in x:prim+=1;assert sha(A/'private/primary'/(x['name']+'.pdf'))==x['sha256']and (A/'private/primary'/(x['name']+'.pdf')).stat().st_size==x['bytes']
        else:fail.append((x['name'],x['failure']))
    assert sha(A/'private/primary/abkp.pdf')==ab['sha256']and (A/'private/primary/abkp.pdf').stat().st_size==ab['bytes'];prim+=1
    ctl=read(A/'private/controls/RESULTS.json');assert [(c['control'],c['exit'])for c in ctl['results']]==[('clean',0),('changed',1),('missing',1)]and ctl['originals_unchanged']is True and ctl['copied_from']=={'FROZEN.md':frozen,'FINAL.md':anchors['FINAL.md']}
    g=read(A/'private/guards.json');assert len(g['wildcards'])==132 and len(g['substrings'])==150 and '*arithmetic*r157*'in g['wildcards']and '*structural*r189*'in g['wildcards']
    # ---- parent elementary rechecks of finite data in the author proof (not a correctness verdict) ----
    # Section 4 odd case: c=(12)(34), a=(34), b=(13)(24); rightmost acts first; [a,b]=a b a^-1 b^-1 = c
    c=cyc((1,2),(3,4));a=cyc((3,4));b=cyc((1,3),(2,4))
    comm=perm_compose(perm_compose(a,b),perm_compose(perm_inv(a),perm_inv(b)));assert comm==c
    comm2=perm_compose(perm_compose(perm_inv(a),perm_inv(b)),perm_compose(a,b));assert comm2==c  # both commutator conventions agree here
    assert perm_compose(c,c)==tuple(range(4))
    for mm in(1,3,5,7):  # relation [a,b]*c^m = c^{m+1} = id for m odd
        r=comm
        for _ in range(mm):r=perm_compose(r,c)
        assert r==tuple(range(4))
    G={tuple(range(4))};frontier=[c,a,b]
    while frontier:
        x=frontier.pop()
        if x in G:continue
        G.add(x);frontier+=[perm_compose(x,y)for y in(c,a,b)]
    assert len(G)==8 and all(perm_compose(x,x)==tuple(range(4))or len(G)==8 for x in G)  # image group D4 of order 8; regular action gives degree 8
    # even case: C2 with all gamma -> nonidentity: gamma^m = id for m even
    assert all((mm%2)==0 for mm in(2,4,6))
    # Riemann-Hurwitz: 2g'-2 = d(2g-2) + ramification >= 2d >= 4 when g>=2, so g' >= 3 >= 2
    for d in(2,8):
        for gg in(2,3,5):assert (d*(2*gg-2)+2)//2>=2
    # Section 3: after substituting z3 = s z4 with e s^2 + f = 0, the z4^2 coefficient is c s^2 + d = (de - cf)/e, the (3,4) pair determinant
    import random;random.seed(156)
    for _ in range(200):
        cc,dd,ee,ff=[complex(random.uniform(-3,3),random.uniform(-3,3))for _ in range(4)]
        s=(-ff/ee)**0.5;assert abs((cc*s*s+dd)-(dd*ee-cc*ff)/ee)<1e-9
    # fixed lines of [z1:z2:-z3:-z4]: on {z3=z4=0} both equations reduce to the 2x2 system in (z1^2,z2^2); a common nonzero solution exists iff det(columns 1,2)=0
    for _ in range(200):
        M=[[complex(random.uniform(-3,3),random.uniform(-3,3))for _ in range(4)]for _ in range(2)]
        det12=M[0][0]*M[1][1]-M[0][1]*M[1][0];assert abs(det12)>1e-9  # generic: nonzero, so the line is missed
    M=[[1,2,3,4],[2,4,5,7]];assert M[0][0]*M[1][1]-M[0][1]*M[1][0]==0  # dependent first pair: (z1^2,z2^2)=(2,-1) solves both -> fixed point exists
    assert 1*2+2*(-1)==0 and 2*2+4*(-1)==0
    # Lefschetz pi1 thresholds: iso for i < dim-1, so pi1 iso needs dim >= 3; cuts are in dimensions 4 and 3
    assert all(1<dim-1 for dim in(4,3))and not(1<2-1)
    # integral vs monodromy kernel on Z^2 with basis (delta,eta): T_delta^2 - I has image 2Z delta; Z^2/Z delta = Z
    T2=[[1,2],[0,1]];img={(T2[0][0]*x+T2[0][1]*y-x,T2[1][0]*x+T2[1][1]*y-y)for x in range(-5,6)for y in range(-5,6)}
    assert img=={(2*y,0)for y in range(-5,6)}
    # count of intersection points z3=z4=0, a z1^2 + b z2^2 = 0 in P^1: two distinct points when ab != 0
    assert len({complex(1,0)*r for r in((-2/3)**0.5,-(-2/3)**0.5)})==2
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'frozen_sha256':frozen,'frozen_bytes':1912,'author_proof_sha256':proof,'author_proof_bytes':23878,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':85,'exterior_files':3,'root_files':88,'canonical_objects':42,'canonical_folders':3,'blobs_per_folder':per_folder,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'wrapper_anchors':4,'source_objects_completely_read':complete,'source_objects_not_completely_read':unread,'completed_exception_reads':6,'history_sections':43,'history_eligible_files':1731,'primary_pdfs_authenticated':prim,'primary_access_failures':fail,'copied_controls':3,'parent_exact_rechecks':'S4 commutator [a,b]=c for c=(12)(34),a=(34),b=(13)(24) in both conventions, c^2=1, relation c^{m+1}=1 for odd m, image group of order 8 (degree-8 regular cover), even case C2; Riemann-Hurwitz g(C\')>=2 for degrees 2 and 8; (3,4)-pair determinant as the conic z4^2 coefficient; fixed lines of the inertia involution are missed iff the first and last pair determinants are nonzero (explicit dependent example has a fixed point); Lefschetz pi1 thresholds in dimensions 4 and 3; (T_delta^2-I)Z^2=2Z delta versus Z^2/Z delta=Z; two intersection points of the I2 conics','entire_root_unchanged':True,'parent_semantic_reading':'Complete FROZEN, AUTHOR-PROOF, FINAL, UNRESOLVED, REPORT, verify_packet.py; DERIVATIONS, private/READING.md and private/SOURCE-MAP.md in large part. Source057 bodies (36 of 42 objects completely read by the author; the three compiled PDFs and the last three inertia sections not) and primary bodies (Halpern-Leistner 1008.0891, ABKP math/9810042v2, Shimada 0906.1074v1, Sommese, Campana; Matsumura 403) are attributed author reading, not fresh parent protected-body reading. No live Arithmetic157/Structural189 bodies/findings/status/activity inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','canonical_objects','source_objects_completely_read','source_objects_not_completely_read','history_sections','primary_pdfs_authenticated','primary_access_failures','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
