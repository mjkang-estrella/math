#!/usr/bin/env python3
"""Read-only Arithmetic158 discovery intake; artifact checks and finite rechecks only, no mathematical gate."""
import cmath,collections,datetime,hashlib,importlib.util,json,random,re,shutil,stat,subprocess,tempfile
from fractions import Fraction as Fr
from math import gcd
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r158';K=A/'packet';V=K/'private'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
ENV={'PYTHON_COLORS':'0','PATH':'/usr/bin:/bin'}
def verifier(root,F,M,R):
    return subprocess.run(['python','-I','-B',str(K/'verify_packet.py'),'--root',str(root),'--final-sha256',F,'--manifest-sha256',M,'--report-sha256',R],cwd=P,capture_output=True,text=True,env=ENV)
def ramanujan_projector_check(m,d):
    # e_d=(1/m) sum_k c_d(k) Theta^k with c_d(k) the Ramanujan sum is the projector onto the primitive-d eigenspaces of the cyclic shift Theta of order m; m e_d is integral
    n=m;Th=[[1 if (i-j)%n==1 else 0 for j in range(n)]for i in range(n)]
    def matpow(M,k):
        R=[[1 if i==j else 0 for j in range(n)]for i in range(n)]
        for _ in range(k):R=[[sum(R[i][t]*M[t][j]for t in range(n))for j in range(n)]for i in range(n)]
        return R
    c=[sum(cmath.exp(-2j*cmath.pi*a*k/d)for a in range(d)if gcd(a,d)==1).real for k in range(m)]
    assert all(abs(x-round(x))<1e-9 for x in c)
    c=[int(round(x))for x in c];E=[[Fr(0)]*n for _ in range(n)];pw=matpow(Th,0)
    for k in range(m):
        for i in range(n):
            for j in range(n):E[i][j]+=Fr(c[k],m)*pw[i][j]
        pw=[[sum(pw[i][t]*Th[t][j]for t in range(n))for j in range(n)]for i in range(n)]
    assert all((m*E[i][j]).denominator==1 for i in range(n)for j in range(n))
    E2=[[sum(E[i][t]*E[t][j]for t in range(n))for j in range(n)]for i in range(n)];assert E2==E
    tr=sum(E[i][i]for i in range(n));phi=sum(1 for a in range(d)if gcd(a,d)==1);assert tr==phi
    # eigenvalue test: E acts as identity on v_a=(zeta^{a j})_j for primitive a, zero for non-primitive-d eigenvectors
    for a in range(m):
        v=[cmath.exp(2j*cmath.pi*a*j/m)for j in range(n)];Ev=[sum(float(E[i][j])*v[j]for j in range(n))for i in range(n)]
        prim=(m//gcd(a,m)==d);assert all(abs(Ev[i]-(v[i]if prim else 0))<1e-8 for i in range(n))
def main():
    anchors=read(A/'ANCHORS.json');F,M,R=anchors['FINAL'],anchors['MANIFEST'],anchors['REPORT']
    assert (F,M,R)==('1f8f7d052a0ef34b4784ace508bbd4edeaa7ab7a74e66c84cc2e01ca1366e0ac','34d50e41847294b963fe154f0ce582cb94cfd64fc0d2c67e874264083ddb02ac','4a4ba1e941dc1ab69a9a0c9994a1fe8b585ceb4f9b30e84f301ddcc6ea736919')
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode)
    assert sha(K/'FINAL.md')==F and sha(A/'MANIFEST.json')==M and sha(A/'REPORT.md')==R
    run=verifier(A,F,M,R);assert run.returncode==0 and not run.stderr
    out=json.loads(run.stdout);assert out=={'artifact_integrity':'matched explicit anchors and exact file set','bytes':6149931,'files':87,'mathematical_grade':'not assigned'}==read(A/'VERIFY.json')
    m=read(A/'MANIFEST.json');assert m['format']=='r158-exact-packet-v1'and m['file_count']==87==len(m['files'])and m['total_bytes']==6149931==sum(x['bytes']for x in m['files']);names={x['path']for x in m['files']}
    assert {'FINAL.md','notes/00-research-state.md','notes/01-operative-comparison.md','notes/02-once-squared-reduction.md','notes/03-conductor-and-cancellation.md','notes/calculation-values.json','verify_packet.py','private/READING-ISOLATION.md','private/authoritative-brief.txt'}<=names
    for x in m['files']:assert (K/x['path']).stat().st_size==x['bytes']and sha(K/x['path'])==x['sha256']
    rootfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};ctrl={f for f in rootfiles if f.startswith('copied-controls/')}
    assert rootfiles-ctrl=={'packet/'+n for n in names}|{'MANIFEST.json','REPORT.md','ANCHORS.json','VERIFY.json','select_authored.py','select_authored_expanded.py'}and len(rootfiles)==97 and len(ctrl)==4
    assert not any(p.is_symlink()for p in A.rglob('*'))
    assert (A/'select_authored.py').read_bytes()==(V/'select_authored.py').read_bytes()and (A/'select_authored_expanded.py').read_bytes()==(V/'select_authored_expanded.py').read_bytes()
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    F1='preprints/Ambiently-homeomorphic-isolated-hypersurfaces-of-multiplicities-two-and-three-September-24-2026/';F2='preprints/Ambiently-homeomorphic-isolated-hypersurface-germs-in-C4-with-multiplicities-four-and-five-September-27-2026/'
    auth=read(V/'authentication.json');assert len(auth)==31;per=collections.Counter()
    for x in auth:
        e=lookup[x['path']];p=V/'upstream'/x['path'];d=p.read_bytes();per[x['path'].split('/')[1]]+=1
        assert x['authenticated']is True and x['type']=='blob'==e['type']and len(d)==x['size']==e['size']and x['sha']==e['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()and sha(p)==x['sha256']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert per=={F1.split('/')[1]:16,F2.split('/')[1]:15}
    for fo in(F1,F2):assert sorted(k for k,e in lookup.items()if k.startswith(fo)and e['type']=='blob')==sorted(x['path']for x in auth if x['path'].startswith(fo))
    assert sum(1 for k in lookup if k.startswith(F1))==22 and sum(1 for k in lookup if k.startswith(F2))==18
    st=read(V/'selected-tree.json');assert sorted((e['path'],e['sha'],e['size'])for e in st)==sorted((lookup[x['path']]['path'],lookup[x['path']]['sha'],lookup[x['path']]['size'])for x in auth)
    for w,sz,bl in((F1+'build/paper.tex',1014,'47218dcfbc946c9ec1bcdef33e0599588a81f9bb'),(F2+'build/paper.tex',903,'719196090775ef43a214f6d2ba08870dd4045283')):assert lookup[w]['size']==sz and lookup[w]['sha']==bl
    se=read(V/'source-reading-extents.json');assert len(se)==31 and {x['path']for x in se}=={x['path']for x in auth}
    full=[x for x in se if x['status']=='complete text body'];assert len(full)==28 and all(x['semantic_read']==[[0,x['bytes']]]and lookup[x['path']]['size']==x['bytes']and x['authenticated_git_blob']==lookup[x['path']]['sha']for x in full)
    assert sorted(x['path'].split('/')[-1]for x in se if x['status']!='complete text body')==['explicit-relation.json','paper.pdf','paper.pdf']
    ie=read(V/'include-edges.json');assert len(ie)==23 and collections.Counter(e['operation']for e in ie)=={'input':20,'bibliography':2,'lstinputlisting':1}
    brief=V/'authoritative-brief.txt';assert brief.read_bytes()==(B/'expanded-target-2026-10-17/fresh-arithmetic-r158-brief.txt').read_bytes()and sha(brief)=='5f11a96f0dc47112db119cd7dcaab1b6a7db7e7262c9a8d93e6c6993950d11c5'and brief.stat().st_size==27810
    assert (V/'direct-AGENTS.md').read_bytes()==(P/'AGENTS.md').read_bytes()and (V/'acceptance-exact.txt').read_bytes()==span(P/'frontier/NEW-TEN-2026-10-14.md',4801,6347)
    assert (V/'source059-catalogue.txt').read_bytes()==span(P/'sources/CONTENTS.md',105150,106786)and (V/'source059-catalogue.txt').stat().st_size==1636
    assert read(V/'upstream-config.json')==read(P/'sources/upstream.json')
    ce=read(V/'completed-exceptions.json');assert len(ce)==6
    for i,x in enumerate(ce):
        o=P/x['path'];assert 'r157'in x['path']and o.stat().st_size==x['bytes']and sha(o)==x['sha256']and (V/f'completed-exception-{i}.txt').read_bytes()==o.read_bytes()
    hx=read(V/'history-extents.json');assert len(hx)==3
    for x in hx:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and (V/x['copy']).read_bytes()==d and not any(t in x['path']for t in('r156','r157','r158','r189','r190','r191'))
    nav=read(V/'history-navigation.json');nav2=read(V/'history-navigation-expanded.json');assert nav['eligible_utf8']==nav2['eligible_utf8']==1692 and nav['nonutf8']==nav2['nonutf8']==12 and len(nav['hits'])==6 and len(nav2['hits'])==185
    for x in nav['hits']+nav2['hits']:assert (P/x['path']).stat().st_size==x['bytes']and sha(P/x['path'])==x['sha256']
    ac=read(V/'primary/access.json');assert [x['name']for x in ac]==['kirschmer','rapinchuk','generation','sakamoto','saeki1989']
    for x in ac:
        pdf=V/'primary'/(x['name']+'.pdf');assert pdf.stat().st_size==x['bytes']and sha(pdf)==x['sha256']and x['extract_exit']==0 and (V/'primary'/(x['name']+'.txt')).stat().st_size>0
    assert {n:(V/'primary'/n).stat().st_size for n in('kirschmer.txt','sakamoto.txt','saeki1989.txt','generation.txt','rapinchuk.txt')}=={'kirschmer.txt':29476,'sakamoto.txt':12192,'saeki1989.txt':16467,'generation.txt':78634,'rapinchuk.txt':84552}  # READING-ISOLATION extents: full for the first three, [0,30501) and [0,56500) for the last two
    ctl=read(V/'artifact-controls.json');assert [(c['control'],c['expected_exit'],c['observed_exit'])for c in ctl['controls']]==[('unaltered copied files',0,0),('modified copied body',1,1),('missing copied body',1,1),('unexpected hidden body',1,1),('incorrect detached anchor',1,1),('restored copied files',0,0)]
    fx=A/'copied-controls';fa=(sha(fx/'packet/FINAL.md'),sha(fx/'MANIFEST.json'),sha(fx/'REPORT.md'))
    good=verifier(fx,*fa);assert good.returncode==0 and json.loads(good.stdout)==json.loads(ctl['controls'][0]['stdout'])
    with tempfile.TemporaryDirectory()as td:
        t=Path(td)/'fx';shutil.copytree(fx,t);(t/'packet/calculation-values.json').write_bytes(b'{}');bad=verifier(t,*fa);assert bad.returncode==1 and json.loads(bad.stdout)==json.loads(ctl['controls'][1]['stdout'])
        shutil.rmtree(t);shutil.copytree(fx,t);(t/'packet/.unexpected').write_bytes(b'x');hid=verifier(t,*fa);assert hid.returncode==1 and json.loads(hid.stdout)==json.loads(ctl['controls'][3]['stdout'])
    wrong=verifier(fx,'0'*64,fa[1],fa[2]);assert wrong.returncode==1 and json.loads(wrong.stdout)==json.loads(ctl['controls'][4]['stdout'])
    g=read(V/'guards.json');assert len(g['wildcards'])==304 and len(g['substrings'])==150 and g['own_root']=='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r158'and {'*structural*r191*','*arithmetic*r156*','*arithmetic*r157*','*structural*r190*'}<=set(g['wildcards'])and 'publication'in g['substrings']
    assert {'*arithmetic*151*','*arithmetic*152*','*analytic*151*','*structural*152*'}<=set(g['wildcards'])  # no-r twins installed
    # Parent rerun of the source relation verifier on a temporary copy (finite evidence for the displayed relation only; not a gate)
    ero=read(V/'explicit-relation-observed.json');cv=read(K/'notes/calculation-values.json')
    with tempfile.TemporaryDirectory()as td:
        t=Path(td)/'verification';shutil.copytree(V/'upstream'/F1/'verification',t)
        assert sha(t/'support/explicit-relation.json')==ero['relation_file_sha256']
        r=subprocess.run(['python','-I','-B',str(t/'validation/explicit_relation.py')],cwd=td,capture_output=True,text=True,env=ENV,timeout=600);assert r.returncode==0 and not r.stderr
        rep=json.loads(r.stdout)
    for k in('verification_passed','d','d_power_of_three','D','support_size','sum_e','sum_abs_e','coefficient_gcd','positive_coefficients','negative_coefficients','raw_factorizations_performed','largest_raw_integer','largest_prime_divisor','relation_file_sha256','chain_checks','seed_construction','final_construction'):assert rep[k]==ero[k],k
    assert rep['first_product_residual_valuations']=={}==ero['first_product_residual_valuations']and rep['second_product_residual_valuations']=={}==ero['second_product_residual_valuations']
    s0=int(rep['seed_construction']['ambient_dimension_s0']);E=int(rep['sum_e'])
    assert str(s0)==cv['s0_supplied_relation']and int(cv['proposed_N_not_topological_claim'])==2*s0+12 and int(cv['source_N'])==4*s0+16==int(rep['final_construction']['ambient_dimension'])
    assert (2*s0+12)%4==0 and (4*s0+16)%8==0 and rep['final_construction']['hessian_ranks']==[str(16*E),'0']and rep['seed_construction']['hessian_ranks']==[str(4*E),'0']
    assert rep['d']==3**11 and rep['D']==3*rep['d']and rep['support_size']==rep['positive_coefficients']+rep['negative_coefficients']==849
    # Parent finite rechecks of notes 02-03
    assert cv['m']==3**12*5*7*11*13==2659862205 and cv['bad_prime_moduli']=={'3':3**12,'5':5,'7':7,'11':11,'13':13}
    # Z_3^3 cyclic example: U=(2/3)J-I is an orthogonal involution commuting with the 3-cycle, +1 on the trivial and -1 on the cyclotomic component, but nonintegral
    J=[[Fr(1)]*3 for _ in range(3)];I=[[Fr(int(i==j))for j in range(3)]for i in range(3)];U=[[Fr(2,3)*J[i][j]-I[i][j]for j in range(3)]for i in range(3)]
    T=[[Fr(int((i-j)%3==1))for j in range(3)]for i in range(3)];mm=lambda X,Y:[[sum(X[i][t]*Y[t][j]for t in range(3))for j in range(3)]for i in range(3)]
    assert mm(U,U)==I and mm(U,T)==mm(T,U) and [[U[j][i]for j in range(3)]for i in range(3)]==U
    one=[Fr(1)]*3;assert [sum(U[i][j]*one[j]for j in range(3))for i in range(3)]==one and [sum(U[i][j]*[Fr(1),Fr(-1),Fr(0)][j]for j in range(3))for i in range(3)]==[Fr(-1),Fr(1),Fr(0)]and any(x.denominator!=1 for row in U for x in row)
    # Ramanujan-sum projector: m e_d integral, idempotent, rank phi(d), correct eigenspaces (small analogue m=15)
    for d in(3,5,15):ramanujan_projector_check(15,d)
    # relative CM unramifiedness: complex conjugation (-1 mod d) is not in the inertia subgroup {x==1 mod d'} of (Z/d)^* at l, d'=l-free part, whenever 143|d
    for d in(143,3*143,9*5*143,7*11*143,2*143,4*3*5*7*11*13):
        for l in(2,3,5,7,11,13,17):
            dp=d
            while dp%l==0:dp//=l
            assert (-1)%dp!=1%dp
    # reverser calculation R^{-1}CRC: x -> z^{-2} x over a CM field model; z=zeta_3 gives zeta_3
    z=cmath.exp(2j*cmath.pi/3);x=0.37+0.91j;val=(1/z)*((z*(x.conjugate())).conjugate());assert abs(val-z**-2*x)<1e-12 and abs(z**-2-z)<1e-12 and abs(z**-2-1)>1
    # second-tensor-square determinant product over ordered pairs cancels, collisions included
    rnd=random.Random(158);ts=[cmath.exp(2j*cmath.pi*rnd.random())for _ in range(6)];ms=[rnd.randint(1,5)for _ in range(6)]
    prod=1
    for g in range(6):
        for e in range(6):prod*=ts[g]**ms[e]/ts[e]**ms[g]
    assert abs(prod-1)<1e-9
    # alpha/conj(alpha) has norm one and generates I^2 when I=alpha O, I conj(I)=O: norm check in the model
    al=1.3+0.4j;t_=al/al.conjugate();assert abs(t_*t_.conjugate()-1)<1e-12
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':87,'packet_bytes':6149931,'root_files':97,'exterior_files':6,'control_fixture_files':4,'canonical_objects':31,'canonical_folders':2,'blobs_per_folder':[16,15],'tree_entries_per_folder':[22,18],'canonical_folders_exhausted':True,'canonical_matches_complete_pinned_tree':True,'wrapper_anchors':[{'path':F1+'build/paper.tex','bytes':1014,'git_blob':'47218dcfbc946c9ec1bcdef33e0599588a81f9bb'},{'path':F2+'build/paper.tex','bytes':903,'git_blob':'719196090775ef43a214f6d2ba08870dd4045283'}],'source_text_objects_fully_read':28,'source_pdfs_authenticated_only':2,'relation_json_parsed_only':1,'include_edges':23,'direct_reads':4,'catalogue_extent':[105150,106786],'completed_exception_copies':6,'history_extents':3,'history_eligible_utf8':1692,'navigation_hits':[6,185],'primary_pdfs':5,'controls_rerun':4,'guard_wildcards':304,'guard_substrings':150,'source_relation_verifier_rerun':{'support_size':849,'s0_digits':len(str(s0)),'proposed_N_eq_2s0_plus_12':True,'source_N_eq_4s0_plus_16':True,'hessian_rank_16E':True,'residual_valuations_empty':True},'parent_exact_rechecks':'m=3^12*5*7*11*13 and the five conductor moduli; Z_3^3 cyclic control U=(2/3)J-I (orthogonal involution commuting with the 3-cycle, +1/-1 on components, nonintegral); Ramanujan-sum projector m e_d integral idempotent of rank phi(d) with correct eigenspaces for m=15, d in {3,5,15}; relative CM unramifiedness for 143|d at l in {2,...,17}; reverser R^{-1}CRC=z^{-2}; ordered-pair determinant cancellation of the second tensor square; alpha/conj(alpha) norm one; source relation verifier rerun on a temporary copy reproducing all recorded counts and s0','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, ANCHORS, VERIFY, verify_packet.py, notes/00-03, calculation-values.json and the READING-ISOLATION record openings and disclosures. Source059 (28 text objects of both manuscripts) and primary (Kirschmer, Brandhorst-Hofmann, Rapinchuk, Sakamoto, Saeki) operative reading attributed to the child, not fresh parent protected-body reading. Live Structural191 not inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','canonical_objects','completed_exception_copies','history_extents','primary_pdfs','controls_rerun','source_relation_verifier_rerun','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
