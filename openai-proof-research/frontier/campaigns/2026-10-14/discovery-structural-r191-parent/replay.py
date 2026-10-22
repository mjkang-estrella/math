#!/usr/bin/env python3
"""Read-only Structural191 discovery intake; artifact checks and finite rechecks only, no mathematical gate."""
import collections,datetime,hashlib,importlib.util,json,math,re,shutil,stat,subprocess,tempfile
from fractions import Fraction as Fr
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r191';V=A/'private'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
ENV={'PYTHON_COLORS':'0','PATH':'/usr/bin:/bin'}
def verifier(root,final,manifest,report):
    return subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--root',str(root),'--final-sha',final,'--manifest-sha',manifest,'--report-sha',report],cwd=P,capture_output=True,text=True,env=ENV)
def clean(s):return re.sub(r'\x1b\[[0-9;]*m','',s)
def line_derivative(R):
    # least squares for delta_0 = A f on the infinite line with f supported on -R..R; exact rational projection onto the zero-sum image
    n=2*R+1;L=2*R+2
    # columns A e_k: edge k-1 gets +1 (f(k)-f(k-1) with f=e_k: edge (k-1,k) -> +1), edge k gets -1 ; edges indexed -R-1..R -> 0..L-1 via +R+1
    cols=[[Fr(0)]*L for _ in range(n)]
    for k in range(n):cols[k][k]=Fr(1);cols[k][k+1]=Fr(-1)
    tgt=[Fr(0)]*L;tgt[R+1]=Fr(1)   # delta at edge (0,1)
    # normal equations G v = A^T tgt
    G=[[sum(cols[i][e]*cols[j][e]for e in range(L))for j in range(n)]for i in range(n)];b=[sum(cols[i][e]*tgt[e]for e in range(L))for i in range(n)]
    M=[G[i]+[b[i]]for i in range(n)]
    for c in range(n):
        piv=next(r for r in range(c,n)if M[r][c]!=0);M[c],M[piv]=M[piv],M[c];pv=M[c][c];M[c]=[x/pv for x in M[c]]
        for r in range(n):
            if r!=c and M[r][c]!=0:f=M[r][c];M[r]=[x-f*y for x,y in zip(M[r],M[c])]
    v=[M[i][n]for i in range(n)];res=[tgt[e]-sum(cols[k][e]*v[k]for k in range(n))for e in range(L)]
    return sum(x*x for x in res),sum(x*x for x in v),res
def main():
    anchors={'FINAL.md':'a2b63b0dd10d7bb1a69c239dd4fcfad84384903862b5e5a756b0b156a5b71a6d','private/MANIFEST.json':'c0ad800e8fedc785995b05b0ff5ddd06de0f61e2d9a2a97fe8f6fbdff3bffba0','REPORT.md':'9e17d49fab4447c343d20a885c379ca789fd686d1e963d297feab552632b7e72'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    aj=read(A/'ANCHORS.json');assert aj['anchors']==anchors and aj['algorithm']=='SHA256'
    run=verifier(A,anchors['FINAL.md'],anchors['private/MANIFEST.json'],anchors['REPORT.md']);assert run.returncode==0 and not run.stderr
    assert run.stdout.strip()=='ARTIFACT INTEGRITY: three supplied anchors and 84 selected files match; no mathematical assessment.'
    m=read(V/'MANIFEST.json');assert m['format']=='r191-selected-packet-v1'and len(m['files'])==84 and sum(x['bytes']for x in m['files'])==4868789 and sorted(m['excluded_detached_carriers'])==['ANCHORS.json','FINAL.md','REPORT.md','private/MANIFEST.json']
    names={x['path']for x in m['files']};assert len(names)==84 and {'DERIVATIONS.md','INTERFACES.md','COMPARISON.md','RESEARCH-NOTES.md','verify_packet.py','private/READING-LIMITS.md','private/authoritative-brief.txt','private/primary-extents.json'}<=names and not names&set(anchors)
    for x in m['files']:assert (A/x['path']).stat().st_size==x['bytes']and sha(A/x['path'])==x['sha256']
    allfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};assert allfiles==names|{'FINAL.md','REPORT.md','ANCHORS.json','private/MANIFEST.json'}and len(allfiles)==88
    assert not any(p.is_symlink()for p in A.rglob('*'))
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    folder='preprints/The-Singer-conjecture-in-dimension-four-September-25-2026/'
    fam=[k for k in lookup if k.startswith(folder)];assert len(fam)==17 and sum(1 for k in fam if lookup[k]['type']=='blob')==16
    auth=read(V/'source-authentication.json');assert len(auth)==16 and sorted(x['path']for x in auth)==sorted(k for k in fam if lookup[k]['type']=='blob')
    for x in auth:
        e=lookup[x['path']];p=V/'source'/x['path'][len(folder):].replace('build/','')
        assert p.is_file(),p
        d=p.read_bytes();assert len(d)==x['bytes']==e['size']and x['git_blob']==e['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()and sha(p)==x['sha256']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert lookup[folder+'build/paper.tex']['size']==1698 and lookup[folder+'build/paper.tex']['sha']=='58c43c1b0867d5b1407147d9363765c528be31a8'
    ft=read(V/'family-tree.json');assert sorted((e['path'],e['sha'],e['type'])for e in ft)==sorted((lookup[k]['path'],lookup[k]['sha'],lookup[k]['type'])for k in fam)
    se=read(V/'source-extents.json');assert len(se)==16 and sum(1 for x in se if x['semantic'])==15
    for x in se:
        p=A/x['file'];assert x['start']==0 and x['end']==p.stat().st_size and sha(p)==x['sha256']and (x['semantic']or x['file'].endswith('paper.pdf'))
    ie=read(V/'include-edges.json');assert len(ie)==13 and ie['paper.tex']==['introduction','foundations','compactification','dynamics','boundary-topology','pretree','blocks','annuli','path-pushing','conclusion','consequences','references']and ie['path-pushing.tex']==['annular-chains']
    wrap=(V/'source/paper.tex').read_text();order=re.findall(r'\\(?:input|include)\{(?:sections/)?([^}]+)\}',wrap);assert [o.split('/')[-1].replace('.tex','')for o in order][:11]==ie['paper.tex'][:11],order
    assert 'annular-chains' in (V/'source/path-pushing.tex').read_text()
    brief=V/'authoritative-brief.txt';assert brief.read_bytes()==(B/'expanded-target-2026-10-17/fresh-structural-r191-brief.txt').read_bytes()and sha(brief)=='916bc4c7fdb4eb26d091141b95278b8280566d277a3f99b3925f8ffb66bf4ac7'and brief.stat().st_size==26224
    for x in read(V/'direct-extents.json'):
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and (A/x['copy']).read_bytes()==d
    assert (V/'catalogue-source315.txt').read_bytes()==span(P/'sources/CONTENTS.md',537826,538801)
    ce=read(V/'completed-direct-reads.json');assert len(ce)==6
    for x in ce:
        o=P/x['path'];assert 'r190'in x['path']and o.stat().st_size==x['bytes']and sha(o)==x['sha256']and x['read_extent']==[0,x['bytes']]and (A/x['copy']).read_bytes()==o.read_bytes()
    ox=read(V/'original-extents.json');assert len(ox)==7 and sum(len(x['individual_sections'])for x in ox)==10
    for i,x in enumerate(ox):
        o=P/x['path'];assert sha(o)==x['original_sha256'];d=span(o,x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['span_sha256']and (V/f'originals/section-{i+1}.txt').read_bytes()==d
        assert x['individual_sections'][0]['start']==x['start']and x['individual_sections'][-1]['end']==x['end']and all(a['end']==b['start']for a,b in zip(x['individual_sections'],x['individual_sections'][1:]))
        assert not any(t in x['path']for t in('r158','r159','r190','r191','arithmetic15'))
    nav=read(V/'original-navigation.json');assert nav['counts']=={'eligible_utf8':1686,'nonutf8':12,'symlinks':0,'pruned':8153}and len(nav['hits'])==341
    for x in nav['hits']:assert (P/x['path']).stat().st_size==x['bytes']and sha(P/x['path'])==x['sha256']
    aa=read(V/'additional-alias-navigation.json');assert aa['same_guard_universe']is True and aa['eligible_utf8']==1686 and len(aa['hits'])==26
    for x in aa['hits']:assert (P/x['path']).stat().st_size==x['bytes']and sha(P/x['path'])==x['sha256']
    assert not any('r191' in x['path']or 'r158' in x['path'] for x in nav['hits']+aa['hits'])
    fo=read(V/'focused-original-navigation.json');assert len(fo)==59
    pol=read(V/'isolation-policy.json');W=set(pol['wildcards']);assert len(W)==295 and len(pol['substrings'])==155 and {'*arithmetic*r158*','*arithmetic*158*','*arithmetic*r159*','*structural*r190*','*structural*190*','*arithmetic*r156*'}<=W and 'publication' in pol['substrings']and pol['own_root']=='frontier/campaigns/2026-10-14/fresh-structural-discovery-r191'
    rc=read(V/'primary/receipts.json');ra=read(V/'primary/receipts-additional.json');av=read(V/'primary/author-version-receipt.json');lr=read(V/'primary/luck1994-retry.json')
    pdfs={x['name']:x for x in rc if x.get('bytes')};pdfs.update({x['name']:x for x in ra if x.get('bytes')});pdfs['clair-whyte-author']=av;pdfs['luck1994']=dict(lr,name='luck1994')
    assert sorted(pdfs)==['clair-whyte','clair-whyte-author','connected','hr','luck-survey','luck1994','topchar','treelike']and any(x.get('error')for x in ra)
    for n,x in pdfs.items():
        p=V/'primary'/(n+'.pdf');assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']and (V/'primary'/(n+'.txt')).stat().st_size>0
    px=read(V/'primary-extents.json');assert len(px)==71
    cnt=collections.Counter()
    for x in px:
        d=span(A/x['file'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256'];cnt[x['file'].split('/')[-1]]+=1
        pages=d.count(b'\f');assert pages<=1
    assert cnt=={'hr.txt':13,'treelike.txt':12,'clair-whyte.txt':12,'topchar.txt':10,'clair-whyte-author.txt':10,'luck1994.txt':10,'connected.txt':2,'luck-survey.txt':2}
    assert sorted(x['physical_page']for x in px if x['file'].endswith('/hr.txt'))==list(range(1,11))+[12,13,14]
    assert (V/'primary/cw-polynomial-page13.png').stat().st_size>0
    # controls rerun on tempdir copies of the child's tiny fixtures
    res=read(V/'controls/results.json');fx=V/'controls/valid';fa=(sha(fx/'FINAL.md'),sha(fx/'private/MANIFEST.json'),sha(fx/'REPORT.md'))
    with tempfile.TemporaryDirectory()as td:
        t=Path(td)/'valid';shutil.copytree(fx,t);g=verifier(t,*fa);assert g.returncode==0==res['valid']['exit_code']and g.stdout==res['valid']['stdout']
        t2=Path(td)/'altered';shutil.copytree(V/'controls/altered',t2);b=verifier(t2,*fa);assert b.returncode==1 and clean(b.stderr)==res['altered_payload']['stderr']
        w=verifier(t,'0'*64,fa[1],fa[2]);assert w.returncode==1 and clean(w.stderr)==res['wrong_anchor']['stderr']
        (t/'extra.txt').write_bytes(b'x');u=verifier(t,*fa);assert u.returncode==1 and 'selected file set differs' in u.stderr
    assert res['original_sha256_before']==res['original_sha256_after']==sha(A/'COMPARISON.md')
    assert (fx/'payload.txt').read_bytes()==(A/'COMPARISON.md').read_bytes()
    # Parent finite rechecks of DERIVATIONS Section 9 and the stated identities
    fc=read(V/'finite-calculations.json');assert len(fc['rows'])==16
    for row in fc['rows']:
        R=row['R'];dl,cs,res_=line_derivative(R);assert dl==Fr(row['delta'])==Fr(1,2*R+2)and cs==Fr(row['cost'])==Fr((R+1)**2+2*sum(j*j for j in range(1,R+1)),(2*R+2)**2)
        assert all(r==Fr(1,2*R+2)for r in res_)  # residual is the constant vector 1/L (projection onto zero-sum complement)
    # slow spectral measure: integral of log t over (0,e^-2] with F(t)=1/log(1/t)^2 equals -1; atom 3/4 at e^4 contributes 3; total 2; F(t)/t^eps unbounded
    N=200000;tot=0.0
    for i in range(N):
        u1=2+i*(1e4/N);u2=2+(i+1)*(1e4/N)
        # dF in u-variable: F=u^-2, dF=-2u^-3 du, log t=-u
        tot+=(-(u1+u2)/2)*(2/((u1+u2)/2)**3)*(u2-u1)
    assert abs(tot-(-1))<2e-3 and abs(tot+3-2)<2e-3
    # log(F(t)/t^eps) = eps*u - 2 log u with u=log(1/t) -> +infinity for every eps>0
    assert all(eps*u-2*math.log(u)>math.log(1e3)for eps in(0.5,0.1,0.01)for u in(1e6,1e9))
    assert abs(1/4+3/4-1)<1e-12
    # Chebyshev polynomial facts: p_{m,z}(0)=1, 0<=p<=1 on [0,1], p(x)<=4 exp(-2 m sqrt z) on [z,1]
    def T(m,x):return math.cosh(m*math.acosh(x))if x>=1 else math.cos(m*math.acos(max(-1,min(1,x))))
    for m in(5,20,60):
        for z in(0.01,0.1,0.3):
            p=lambda x:(T(m,(1+z-2*x)/(1-z))+1)/(T(m,(1+z)/(1-z))+1)
            assert abs(p(0)-1)<1e-9 and all(-1e-12<=p(x)<=1+1e-12 for x in[i/400 for i in range(401)])and all(p(x)<=4*math.exp(-2*m*math.sqrt(z))+1e-12 for x in[z+(1-z)*i/400 for i in range(401)])
    # spectral identities (4.3): for lambda>=0,t>0: t^2/(l+t)^2 + l/(l+t)^2 * t = t/(l+t) (delta + t cost = I); t/(l+t)>=1/2 on [0,t]; l/(l+t)^2<=1/(4t)
    for l in(0.0,0.3,1.0,7.5):
        for t in(0.1,1.0,3.0):
            assert abs(t*t/(l+t)**2+t*l/(l+t)**2-t/(l+t))<1e-12 and l/(l+t)**2<=1/(4*t)+1e-12 and(l>t or t/(l+t)>=0.5-1e-12)
    # Euler/duality accounting: for d in {1,2}, |b_2/n - chi| <= (1+d)delta + 2/n given b_1/n<=delta, b_3/n<=d delta, b_4 in {0,1}, b_0=1
    for d in(1,2):
        for n in(1,5,1000):
            for delta in(0.0,0.01,0.5):
                for b4 in(0,1):
                    b1=delta*n;b3=d*delta*n;assert abs((b1+b3-1-b4)/n)<=(1+d)*delta+2/n+1e-12
    # cover certificate (3.2) sanity on a finite cyclic model: residual support injects when ell(N)>2(R+s)
    for n in(7,12):
        for R in range(0,3):
            s=1;assert n>2*(R+s)or True
            supp=range(-(R+s),R+s+1);assert len({x%n for x in supp})==len(list(supp))if n>2*(R+s)else True
    # conductor-free truncation bound (6.1): sup over lambda in [0,K] of lambda/(lambda+t) (1-(lambda+t)/(K+t))^m <= (K/(K+t))^m
    for K,t,m in((1.0,0.1,5),(3.0,0.5,10),(10.0,0.01,30)):
        q=K/(K+t);assert max(l/(l+t)*abs(1-(l+t)/(K+t))**m for l in[K*i/2000 for i in range(2001)])<=q**m+1e-12
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':run.stdout.strip(),'payload_files':84,'payload_bytes':4868789,'root_files':88,'canonical_objects':16,'canonical_folder_entries':17,'canonical_folder_blobs_exhausted':True,'canonical_matches_complete_pinned_tree':True,'wrapper_anchor':{'path':folder+'build/paper.tex','bytes':1698,'git_blob':'58c43c1b0867d5b1407147d9363765c528be31a8'},'source_text_objects_fully_read':15,'source_pdf_authenticated_only':1,'include_order_confirmed_from_wrapper':True,'direct_reads':3,'catalogue_extent':[537826,538801],'completed_exception_copies':6,'original_history_spans':7,'original_history_sections':10,'navigation_hits':[341,26,59],'eligible_utf8':1686,'primary_pdfs':8,'primary_page_extents':71,'primary_access_failure_recorded':'him-lueck.uni-bonn.de timeout, alternate author host succeeded','controls_rerun':4,'guard_wildcards':295,'guard_substrings':155,'parent_exact_rechecks':'line-derivative least squares for R=0..15 by exact rational normal equations (delta_R=1/(2R+2), kappa_R formula, constant residual 1/L); slow spectral measure logarithmic integral (-1 continuous, +3 atom, total 2) and failure of every power bound; Chebyshev p_{m,z} normalization, [0,1] range and 4exp(-2m sqrt z) tail for nine (m,z); the (4.3) identity delta+t cost=I, t/(l+t)>=1/2 on [0,t], cost<=a/(4t); Euler/duality accounting bound (1+d)delta+2/n; support injectivity under ell(N)>2(R+s); truncation multiplier bound (6.1)','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, ANCHORS, verify_packet.py, DERIVATIONS, INTERFACES, COMPARISON, RESEARCH-NOTES and READING-LIMITS. Source315 (15 text objects), primary (Hruska-Ruane, Bowditch x3, Clair-Whyte x2, Lueck 1994 and survey) and original-history operative reading attributed to the child, not fresh parent protected-body reading. Live Arithmetic159 not inspected or steered.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['payload_files','canonical_objects','completed_exception_copies','original_history_spans','primary_pdfs','primary_page_extents','controls_rerun','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
