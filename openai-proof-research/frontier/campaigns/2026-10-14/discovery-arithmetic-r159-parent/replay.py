#!/usr/bin/env python3
"""Read-only Arithmetic159 discovery intake; artifact checks and finite rechecks only, no mathematical gate."""
import collections,datetime,hashlib,importlib.util,json,math,shutil,stat,subprocess,tempfile
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-arithmetic-discovery-r159';K=A/'packet';V=K/'private'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
FOLDER='preprints/Global-Spherical-Shells-on-Minimal-Surfaces-of-Class-VII-September-24-2026/'
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
ENV={'PYTHON_COLORS':'0','PATH':'/usr/bin:/bin'}
def verifier(packet,manifest,report,F,M,R):
    return subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--packet',str(packet),'--manifest',str(manifest),'--report',str(report),'--final-sha256',F,'--manifest-sha256',M,'--report-sha256',R],cwd=P,capture_output=True,text=True,env=ENV)
# --- finite recurrence helpers (note 02, (3)-(4)) ---
def coeffs(s,N):
    b=len(s);L=b+1;a=[1]
    for j in range(1,N):a.append(sum(a[j-d]for d in range(1,min(L,j)+1)if d<=s[(j-d)%b]))
    return a
def companion(s,j):
    b=len(s);L=b+1
    return [[int(d<=s[(j-d)%b])for d in range(1,L+1)]]+[[int(c==i-1)for c in range(L)]for i in range(1,L)]
def mm(X,Y):return [[sum(x*y for x,y in zip(r,c))for c in zip(*Y)]for r in X]
def period_matrix(s):
    L=len(s)+1;Am=[[int(i==j)for j in range(L)]for i in range(L)]
    for j in range(1,len(s)+1):Am=mm(companion(s,j),Am)
    return Am
def spectral_radius(Am):
    # power iteration on a nonnegative matrix with a positive start vector; adequate for the finite recheck
    n=len(Am);v=[1.0]*n;r=1.0
    for _ in range(4000):
        w=[sum(Am[i][j]*v[j]for j in range(n))for i in range(n)];nw=max(w)
        if nw==0:return 0.0
        v=[x/nw for x in w];r=nw
    return r
def charpoly_eval(Am,x):
    n=len(Am);Mx=[[Fr(Am[i][j])-(x if i==j else 0)for j in range(n)]for i in range(n)]
    # Fraction Gaussian elimination determinant
    det=Fr(1)
    for c in range(n):
        piv=next((r for r in range(c,n)if Mx[r][c]!=0),None)
        if piv is None:return Fr(0)
        if piv!=c:Mx[c],Mx[piv]=Mx[piv],Mx[c];det=-det
        det*=Mx[c][c]
        for r in range(c+1,n):
            f=Mx[r][c]/Mx[c][c];Mx[r]=[Mx[r][k]-f*Mx[c][k]for k in range(n)]
    return det*(-1)**n  # det(xI-A)
def main():
    anchors=read(A/'ANCHORS.json');F,M,R=anchors['FINAL_SHA256'],anchors['MANIFEST_SHA256'],anchors['REPORT_SHA256']
    assert (F,M,R)==('e5f327b44ee3726674588a65e776d334dfb3e13cee6a681dd20cd6ffb400224c','319ee2c658c9ca02b407de93dbc559a71dd6d588fcbe8ca30c1d383a60554616','5af84dd1b8cba3cbe7e49f1eb4c98b0b384103ec68e93738c4c8d9487ae7f225')
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode)
    assert sha(K/'FINAL.md')==F and sha(A/'MANIFEST.json')==M and sha(A/'REPORT.md')==R and sha(A/'verify_packet.py')=='7094a4e83d5038d5b981c52831ab7b79105b50affb6a3faf04662049b7c7ac05'and sha(A/'copied-controls/results.json')=='35877ab6ba6e0cb9a0f8948125429cc2ddc165972748f421759eeccde363440f'
    run=verifier(K,A/'MANIFEST.json',A/'REPORT.md',F,M,R);assert run.returncode==0 and not run.stderr
    out=json.loads(run.stdout);vj=read(A/'VERIFY.json');assert out=={'artifact_integrity':'matches explicit detached anchors','bytes':4510179,'files':56,'mathematical_gate':False}==json.loads(vj['stdout'])and vj['exit']==0 and vj['stderr']==''
    m=read(A/'MANIFEST.json');assert m['schema']=='r159-exact-packet-v1'and len(m['files'])==56 and sum(x['bytes']for x in m['files'])==4510179;names={x['path']for x in m['files']}
    assert {'FINAL.md','notes/00-source-mechanism.md','notes/01-primary-payment.md','notes/02-triangular-and-spectral-reduction.md','notes/03-relative-operation.md','notes/calculation-values.json','notes/recurrence_calculation.py','private/READING-ISOLATION.md','private/authoritative-brief.txt','private/guard.py','private/guard-policy.json'}<=names
    for x in m['files']:p=K/x['path'];assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']and stat.S_IMODE(p.stat().st_mode)==x['mode']
    rootfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};ctrl={f for f in rootfiles if f.startswith('copied-controls/')}
    assert rootfiles-ctrl=={'packet/'+n for n in names}|{'MANIFEST.json','REPORT.md','ANCHORS.json','VERIFY.json','verify_packet.py','guard.py'}and len(rootfiles)==67 and len(ctrl)==5
    assert not any(p.is_symlink()for p in A.rglob('*'))and (A/'guard.py').read_bytes()==(V/'guard.py').read_bytes()
    # pinned tree and canonical blobs: single folder exhausted
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    auth=read(V/'source-authentication.json');assert len(auth)==11
    for x in auth:
        e=lookup[x['path']];p=P/x['local'];d=p.read_bytes();assert x['path'].startswith(FOLDER)and e['type']=='blob'and len(d)==x['bytes']==e['size']and x['git_blob']==e['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()and sha(p)==x['sha256']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert sorted(k for k,e in lookup.items()if k.startswith(FOLDER)and e['type']=='blob')==sorted(x['path']for x in auth)and sum(1 for k in lookup if k.startswith(FOLDER))==14
    st=read(V/'source-tree-selected.json');assert len(st)==15 and sorted((e['path'],e['sha'])for e in st)==sorted((e['path'],e['sha'])for k,e in lookup.items()if k==FOLDER[:-1]or k.startswith(FOLDER))
    assert lookup[FOLDER+'build/paper.tex']['size']==16805 and lookup[FOLDER+'build/paper.tex']['sha']=='f79ccb59553aa128043c866d98f9b5a7ae4824b2'
    se=read(V/'source-reading-extents.json');assert len(se)==11 and {x['source_path']for x in se}=={x['path']for x in auth}
    full=[x for x in se if x['status']=='complete semantic reading'];assert len(full)==10 and all(x['semantic_extents']==[[0,x['bytes']]]and lookup[x['source_path']]['size']==x['bytes']for x in full)
    assert [x['local']for x in se if x['status']!='complete semantic reading']==['paper.pdf']
    # include edges reparsed from the wrapper and the cylinder section
    w=(V/'source/build/paper.tex').read_bytes();ie=read(V/'include-edges.json');assert len(ie)==9
    for e in ie:
        src=(V/'source'/e['from']).read_bytes();cmd=b'\\input{'+e['input'].encode()+b'}';assert src[e['byte_start']:e['byte_start']+len(cmd)]==cmd  # byte_start addresses the \input command
    assert [e['input']for e in ie if e['from']=='build/paper.tex']==['glyphtounicode','sections/surfaces.tex','sections/compact-data.tex','sections/weighted.tex','sections/curves.tex','sections/cylinder.tex','sections/conclusion.tex','references.tex']
    assert [l.strip()for l in w.decode().splitlines()if l.strip().startswith('\\input{sections/')]==['\\input{sections/surfaces.tex}','\\input{sections/compact-data.tex}','\\input{sections/weighted.tex}','\\input{sections/curves.tex}','\\input{sections/cylinder.tex}','\\input{sections/conclusion.tex}']
    assert b'\\input{figures/flat-chain.tex}'in (V/'source/build/sections/cylinder.tex').read_bytes()and b'\\input{references.tex}'in w
    # direct reads and brief copy
    brief=V/'authoritative-brief.txt';assert brief.read_bytes()==(B/'expanded-target-2026-10-17/fresh-arithmetic-r159-brief.txt').read_bytes()and sha(brief)=='17b8085045654c0b68bb1b34cca461cf45f32a57efa328e8a6d288f1f247accf'and brief.stat().st_size==26491
    assert (V/'direct-AGENTS.md').read_bytes()==(P/'AGENTS.md').read_bytes()and (V/'acceptance-4801-6347.txt').read_bytes()==span(P/'frontier/NEW-TEN-2026-10-14.md',4801,6347)and read(V/'direct-upstream.json')==read(P/'sources/upstream.json')
    assert hashlib.sha256(span(P/'sources/CONTENTS.md',106786,107733)).hexdigest()=='e12dd05da731177b14393c723a1d2872ce78d7a0ff7cc3554ee0ce3dfae6548e'and not any('catalogue'in n for n in names)  # catalogue span not accessed by the child, as disclosed
    ce=read(V/'completed-exceptions.json');assert len(ce)==6
    for x in ce:
        o=P/x['path'];assert ('r158'in x['path'])and o.stat().st_size==x['bytes']and sha(o)==x['sha256']and (P/x['copy']).read_bytes()==o.read_bytes()and x['copy'].startswith('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r159/packet/private/completed-exceptions/')
    assert sorted(x['path'].split('/')[-1]for x in ce)==sorted(['assessment.md','FINAL.md','01-operative-comparison.md','02-once-squared-reduction.md','03-conductor-and-cancellation.md','READING-ISOLATION.md'])
    hx=read(V/'history-extents.json');assert len(hx)==1 and hx[0]['path']=='proposals/cross_family.md'and (hx[0]['start'],hx[0]['end'])==(19648,22242)
    d=span(P/hx[0]['path'],19648,22242);assert hashlib.sha256(d).hexdigest()==hx[0]['sha256']and (V/'history-original-selection.txt').read_bytes()==d and d.startswith(b'## Rejected combinations')
    nav=read(V/'history-navigation.json');nav2=read(V/'history-navigation-expanded.json');assert nav['eligible_files']==1706 and len(nav['decode_failures'])==12 and len(nav['terms'])==20 and len(nav2['terms'])==16 and len(nav['hits'])==1 and nav2['eligible_utf8']==1694 and len(nav2['hits'])==19
    for x in nav['hits']+nav2['hits']:assert (P/x['path']).stat().st_size==x['bytes']and not any(t in x['path'].casefold()for t in('r158','r159','r160','r191','r192','r193'))
    # primary PDFs, extractions, declared extents
    ac=read(V/'primary/access.json');assert [x['name']for x in ac]==['dt','dot','kato']and ac[2]['error']=='HTTP Error 500: 500'
    for x in ac[:2]:
        pdf=V/'primary'/(x['name']+'.pdf');assert pdf.stat().st_size==x['bytes']and sha(pdf)==x['sha256']and (V/'primary'/(x['name']+'.txt')).stat().st_size==x['extract_bytes']
    pa=read(V/'primary/published-access.json');assert (V/'primary/dt-published.pdf').stat().st_size==pa['bytes']==391196 and sha(V/'primary/dt-published.pdf')==pa['sha256']and pa['pdf']is True
    pe=read(V/'primary-reading-extents.json');assert len(pe['records'])==3
    for r in pe['records']:
        p=V/r['file'];assert p.stat().st_size==r['bytes']and sha(p)==r['sha256']
        tiles=sorted(map(tuple,r['semantic_byte_intervals']+r['unread_byte_intervals']));assert tiles[0][0]==0 and tiles[-1][1]==r['bytes']and all(tiles[i][1]==tiles[i+1][0]for i in range(len(tiles)-1))  # declared read and unread extents tile the file exactly
    assert pe['records'][1]['unread_byte_intervals']==[[0,75173]]and pe['records'][2]['unread_byte_intervals']==[[6500,17812]]and pe['records'][0]['unread_byte_intervals']==[]
    assert all((V/'primary'/n.split(' ')[0]).stat().st_size>0 for n in pe['images_semantically_viewed'])
    # controls rerun on temporary copies
    ctl=read(A/'copied-controls/results.json');assert [(c['control'],c['exit'])for c in ctl]==[('exact-copy',0),('tampered-copy',1),('extra-copy-file',1),('wrong-report-anchor',1)]
    fx=A/'copied-controls';fa=(sha(fx/'packet/FINAL.md'),sha(fx/'MANIFEST.json'),sha(fx/'REPORT.md'));assert fa[0]==F and (fx/'packet/calculation-values.json').read_bytes()==(K/'notes/calculation-values.json').read_bytes()
    good=verifier(fx/'packet',fx/'MANIFEST.json',fx/'REPORT.md',*fa);assert good.returncode==0 and json.loads(good.stdout)==json.loads(ctl[0]['output'])
    with tempfile.TemporaryDirectory()as td:
        t=Path(td)/'fx';shutil.copytree(fx,t);(t/'packet/calculation-values.json').write_bytes(b'{}');bad=verifier(t/'packet',t/'MANIFEST.json',t/'REPORT.md',*fa);assert bad.returncode==1 and json.loads(bad.stdout)==json.loads(ctl[1]['output'])
        shutil.rmtree(t);shutil.copytree(fx,t);(t/'packet/extra.txt').write_bytes(b'x');ex=verifier(t/'packet',t/'MANIFEST.json',t/'REPORT.md',*fa);assert ex.returncode==1 and json.loads(ex.stdout)==json.loads(ctl[2]['output'])
    wrong=verifier(fx/'packet',fx/'MANIFEST.json',fx/'REPORT.md',fa[0],fa[1],'0'*64);assert wrong.returncode==1 and json.loads(wrong.stdout)==json.loads(ctl[3]['output'])
    g=read(V/'guard-policy.json');W=set(g['wildcards'])|set(g['additional_wildcards']);assert len(g['wildcards'])==290 and len(g['additional_wildcards'])==10 and len(g['substrings'])==150 and g['own_root']=='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r159'
    assert {'*structural*r192*','*arithmetic*r158*','*arithmetic*r160*','*structural*r193*','*structural*r191*'}<=W and 'publication'in g['substrings']and any(w.startswith('*arithmetic*1')for w in W)  # no-r twins present
    # --- Parent finite rechecks of notes 02-03 (not gates) ---
    cv=read(K/'notes/calculation-values.json');assert [e['word']for e in cv]==[[1],[2],[2,1],[3,1],[2,2]]
    for e in cv:
        s=e['word'];b=len(s);L=b+1;a=coeffs(s,40);assert a[:24]==e['coefficients_first_24']and period_matrix(s)==e['period_matrix']
        Am=e['period_matrix']
        for x in(Fr(0),Fr(1),Fr(2),Fr(-1),Fr(3,2)):assert sum(Fr(c)*x**i for i,c in enumerate(e['characteristic_polynomial_low_to_high']))==charpoly_eval(Am,x)
        for r,f in enumerate(e['phase_generating_functions']):
            num,den=f['numerator_low_to_high'],f['denominator_low_to_high'];exp=[]
            for k in range(14):
                val=Fr(num[k]if k<len(num)else 0)-sum(den[dd]*exp[k-dd]for dd in range(1,min(len(den)-1,k)+1));exp.append(val/den[0])
            assert exp==[Fr(a[k*b+r])for k in range(14)]
        # triangular class relation (1) with impulse at 0 on the computed prefix: x_0=1, x_j=0 for 1<=j<40
        q=[0]*(40+L)
        for j,aj in enumerate(a):
            q[j]+=aj
            for dd in range(1,s[j%b]+1):q[j+dd]-=aj
        assert q[0]==1 and all(v==0 for v in q[1:40])
        # E_i = C_i + sum_{d=1}^{s_i} E_{i+d} on the prefix (coefficients of E_d obtained by index shift of the same periodic word)
        def E(i,N):  # coefficient vector of E_i on indices [0,N)
            sh=s[i%b:]+s[:i%b];c=coeffs(sh,N-i);return [0]*i+c
        N=30;lhs=E(0,N);rhs=[int(j==0)for j in range(N)]
        for dd in range(1,s[0]+1):rhs=[u+v for u,v in zip(rhs,E(dd,N))]
        assert lhs==rhs
        # monotone, a_j<=2^j, theta_L majorant, exact threshold: partial sums of sum a_j z^j bounded for z<1/rho, diverging at z=1/rho
        assert all(a[j]>=a[j-1]for j in range(1,40))and all(a[j]<=2**j for j in range(40))
        th=2.0
        for _ in range(200):th=th-(sum(th**-dd for dd in range(1,L+1))-1)/(-sum(dd*th**(-dd-1)for dd in range(1,L+1)))
        assert 1<th<2 and all(a[j]<=th**j*(1+1e-9)for j in range(40))
        rho=spectral_radius(Am);assert rho<=th**b+1e-9 and rho<=2**b
        if all(v==1 for v in s):assert abs(rho-1)<1e-9 and a==[1]*40
        else:assert rho>=2**(b/(b+1))-1e-9 and all(a[j+b+1]>=2*a[j]for j in range(40-b-1))
        big=coeffs(s,400*b);ph=[sum(big[k*b+r]for r in range(b))for k in range(400)]  # period sums; rho is the per-period rate
        S_sub=sum(c*(0.98/rho)**k for k,c in enumerate(ph));S_crit=[sum(c*(1/rho)**k for k,c in enumerate(ph[:n]))for n in(100,200,400)]
        assert S_sub<1e6 and S_crit[0]<S_crit[1]<S_crit[2]and S_crit[2]-S_crit[1]>0.5*(S_crit[1]-S_crit[0])  # linear-or-faster growth at the critical point
    # cyclic rotations of a word share the nonzero spectrum (phase independence of rho)
    for s in([3,1],[2,2],[2,1,3],[4,1,2]):
        b=len(s);L=b+1;P0=period_matrix(s)
        for k in range(1,b):
            Pk=period_matrix(s[k:]+s[:k])
            for x in(Fr(1),Fr(2),Fr(-1),Fr(5,2),Fr(7)):assert charpoly_eval(P0,x)*x**0==charpoly_eval(Pk,x)  # same characteristic polynomial for cyclic products of square matrices
    # finite word set: rho bounds hold over ALL words with 1<=s_j<=b+1 for b<=3
    rows=0
    for b in(1,2,3):
        th=2.0;L=b+1
        for _ in range(200):th=th-(sum(th**-dd for dd in range(1,L+1))-1)/(-sum(dd*th**(-dd-1)for dd in range(1,L+1)))
        for s in product(range(1,b+2),repeat=b):
            rho=spectral_radius(period_matrix(list(s)));rows+=1
            assert rho<=th**b+1e-9 and((abs(rho-1)<1e-9)if all(v==1 for v in s)else rho>=2**(b/(b+1))-1e-9)
    assert rows==2+9+64
    # 0/1 lemma: integer solutions of sum x_j(x_j-1)=0 with finitely many nonzero entries have x_j in {0,1}
    assert all(x*(x-1)>0 for x in range(-6,8)if x not in(0,1))
    # tail implication (8) and the one-dimensional measure diagnosis
    eps=0.3;Mv=20.0;assert math.exp(-(eps/2)*Mv)==math.exp(-eps*Mv/2)
    # nu_n=delta_0+exp(cn)delta_{-n}: beta-weighted mass 1+exp((c-beta)n) is unbounded in n for beta<c and bounded for beta>c, while mass on {x>-5} is 1 for n>5
    c=1.0;mass=lambda beta,n:1+math.exp((c-beta)*n)
    assert mass(0.5,200)>mass(0.5,100)>1e20 and all(mass(1.5,n)<2 for n in(10,100,1000))and all(1+(math.exp(c*n)if -n>-5 else 0)==1 for n in(10,100))
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'packet_files':56,'packet_bytes':4510179,'root_files':67,'exterior_files':6,'control_fixture_files':5,'canonical_objects':11,'canonical_folders':1,'blobs_per_folder':[11],'tree_entries_per_folder':[14],'canonical_folders_exhausted':True,'canonical_matches_complete_pinned_tree':True,'wrapper_anchor':{'path':FOLDER+'build/paper.tex','bytes':16805,'git_blob':'f79ccb59553aa128043c866d98f9b5a7ae4824b2'},'source_text_objects_fully_read':10,'source_pdfs_authenticated_only':1,'include_edges':9,'include_order_reparsed':True,'direct_reads':4,'catalogue_extent_not_accessed_by_child':[106786,107733],'completed_exception_copies':6,'history_extents':1,'history_eligible_files':1706,'navigation_hits':[1,19],'primary_pdfs':3,'primary_fetch_failures':['kato HTTP 500'],'controls_rerun':4,'guard_wildcards':300,'guard_substrings':150,'parent_exact_rechecks':'five period matrices, characteristic polynomials (five rational evaluation points), phase generating functions (14 terms each) and 24 coefficients recomputed from recurrence (3); triangular class relation (1) on a 40-term prefix; E_i=C_i+sum_{d<=s_i}E_{i+d} on 30-term prefixes; monotonicity, a_j<=2^j, a_j<=theta_L^j; rho<=theta_L^b<=2^b, rho=1 iff all s_j=1 else rho>=2^{b/(b+1)} and a_{j+b+1}>=2a_j, checked over all 75 words with b<=3; subcritical convergence and critical divergence of sum a_j z^j on 400-term prefixes; cyclic rotations of a word share the characteristic polynomial; 0/1 lemma; tail factor exp(-eps M/2); one-dimensional measure diagnosis 1+exp((c-beta)n)','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, ANCHORS, VERIFY, verify_packet.py, guard.py, notes/00-03 (00-01 in part through display truncation of the long paragraphs), recurrence_calculation.py, calculation-values.json, READING-ISOLATION and the private record schemas. Source060 (10 text objects) and primary (Dloussky-Oeljeklaus-Toma 2003; Dloussky-Teleman arXiv v2 latter presentation and Math. Ann. 2012 published Sections 2-4) operative reading attributed to the child, not fresh parent protected-body reading. Live Structural192 not inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['packet_files','root_files','canonical_objects','completed_exception_copies','history_extents','primary_pdfs','controls_rerun','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
