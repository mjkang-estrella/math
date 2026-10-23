#!/usr/bin/env python3
"""Read-only Structural195 author-nominee intake; artifact checks and finite rechecks only, no mathematical gate."""
import collections,datetime,hashlib,importlib.util,itertools,json,random,re,shutil,stat,subprocess,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r195';V=A/'private'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
FOLDER='preprints/Counterexamples-to-the-Hahn-Wilson-conjecture-at-height-two-September-26-2026/'
WRAPPER=('build/main.tex',14864,'1232983b9757fad0d6fc659478cd6198e52021a5')
FINAL='209a4a78bd9a7354b28f9f379919cb5795abbe62e1897081002461813761d44a';MANIFEST='7233bd5dc5687e25f46bd6e98e84b75558d7a28f18d85968ed902a5fcca004a6';REPORT='31213c2300098babac39267c723a6a9d1545785f282094edc6df6ac9b6b1255a'
FROZEN='823bddbdf60d3827d4f0cbf5684d559de760646b811f1626db497ed1786f8be8'
SECTIONS=['geometry','completion','operator','gluing','obstruction','comparison','transfer','consequences']
def read(p):return json.loads(p.read_bytes())
def lines(p):return [json.loads(l)for l in p.read_text().splitlines()if l.strip()]
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
ENV={'PYTHON_COLORS':'0','PATH':'/usr/bin:/bin'}
def verifier(root,F,M,R):
    return subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--root',str(root),'--final-sha',F,'--manifest-sha',M,'--report-sha',R],cwd=P,capture_output=True,text=True,env=ENV)
def clean(s):return re.sub(r'\x1b\[[0-9;]*m','',s)

# ---------------- parent finite rechecks of retained bookkeeping (independent of the child's text; not gates) ----------------
def gf2(p):
    """F_{p^2}=F_p[i]/(i^2-n) with n a quadratic nonresidue; elements are pairs (a,b)=a+b i."""
    n=next(n for n in range(2,p)if pow(n,(p-1)//2,p)==p-1)
    add=lambda u,v:((u[0]+v[0])%p,(u[1]+v[1])%p)
    mul=lambda u,v:((u[0]*v[0]+n*u[1]*v[1])%p,(u[0]*v[1]+u[1]*v[0])%p)
    elems=[(a,b)for a in range(p)for b in range(p)]
    return elems,add,mul,(0,0),(1,0)
def pmul(f,g,add,mul,zero):
    out=[zero]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):out[i+j]=add(out[i+j],mul(a,b))
    return out
def count_monic_irreducibles(p,d):
    elems,add,mul,zero,one=gf2(p);q=len(elems)
    monic=lambda deg:[list(c)+[one]for c in itertools.product(elems,repeat=deg)]
    reducible=set()
    for a in range(1,d//2+1):
        for f in monic(a):
            for g in monic(d-a):reducible.add(tuple(pmul(f,g,add,mul,zero)))
    total=q**d;return total-len(reducible),(q**d-q)//d if all(d%r for r in range(2,d))else None
def eigen_mult_by_norm_one(p):
    """Multiplication by lambda with lambda^(p+1)=1 on F_{p^2} as an F_p-matrix: char poly (t-lambda)(t-lambda^p), lambda^p=lambda^-1."""
    elems,add,mul,zero,one=gf2(p)
    def pw(u,e):
        r=one
        for _ in range(e):r=mul(r,u)
        return r
    out=[]
    for lam in elems:
        if lam in(zero,one)or pw(lam,p+1)!=one:continue
        M=[list(mul(lam,(1,0))),list(mul(lam,(0,1)))]  # columns are images of basis 1,i
        tr=(M[0][0]+M[1][1])%p;det=(M[0][0]*M[1][1]-M[0][1]*M[1][0])%p
        s=add(lam,pw(lam,p));pr=mul(lam,pw(lam,p));assert s[1]==0 and pr[1]==0  # lambda+lambda^p and lambda^(p+1) lie in F_p
        out.append(tr==s[0]and det==pr[0]and mul(lam,pw(lam,p))==one)  # char poly (t-lambda)(t-lambda^p), lambda^p=lambda^-1
    return len(out)==p and all(out)  # p nontrivial norm-one elements (mu_(p+1) minus 1)
def augmentation_pth_power_zero(p,trials=40):
    """In F_p[Z/p x Z/p] (commutative), every augmentation-ideal element has p-th power zero."""
    G=[(a,b)for a in range(p)for b in range(p)];rng=random.Random(195)
    def gmul(u,v):
        out=collections.Counter()
        for g,a in u.items():
            for hh,b in v.items():out[((g[0]+hh[0])%p,(g[1]+hh[1])%p)]=(out[((g[0]+hh[0])%p,(g[1]+hh[1])%p)]+a*b)%p
        return {g:c for g,c in out.items()if c}
    ok=True
    for _ in range(trials):
        u={}
        for g in G:
            a=rng.randrange(p)
            if a:u[g]=(u.get(g,0)+a)%p;u[(0,0)]=(u.get((0,0),0)-a)%p
        u={g:c for g,c in u.items()if c};r={(0,0):1}
        for _ in range(p):r=gmul(r,u)
        ok&=(r=={})
    return ok
def hilbert_coeffs(e,g,N):
    """Coefficients of (1-z^e)(1-z^g)/((1-z)^2(1-z^3)) up to degree N."""
    num=[0]*(e+g+1);num[0]+=1;num[e]-=1;num[g]-=1;num[e+g]+=1
    den=[0]*6;den[0]=1;den[1]=-2;den[2]=1;den[3]=-1;den[4]=2;den[5]=-1  # (1-z)^2(1-z^3)
    c=[]
    for n in range(N+1):
        s=(num[n]if n<len(num)else 0)-sum(den[k]*c[n-k]for k in range(1,6)if n-k>=0)
        c.append(s)
    return c
def monomial_count_weighted(T):
    """Monomials A^a B^b C^c with a,b,c<T: weight a+b+3c <= 5(T-1) always; count is T^3 (consistency of the weight bound only)."""
    return sum(1 for a in range(T)for b in range(T)for c in range(T)if a+b+3*c<=5*(T-1))==T**3
def smallest_operator_prime():
    """Smallest prime p admitting odd M>=81 with p>16M^2 and 2*floor(M/8)>p^(1/3) (frozen hypothesis is nonvacuous)."""
    def isprime(n):
        if n<2:return False
        if n%2==0:return n==2
        r=int(n**0.5)+1
        return all(n%k for k in range(3,r,2))
    def ok(p):
        for M in range(81,int(p**0.5/4)+2,2):
            if 16*M*M<p and(2*(M//8))**3>p:return M
        return None
    p=16**6
    while True:
        if isprime(p)and ok(p):return p,ok(p)
        p+=1
def parent_rechecks():
    r={}
    r['monic_irreducible_prime_degree_counts']={f'q={p*p},d={d}':count_monic_irreducibles(p,d)for p,d in((3,2),(3,3),(5,2),(5,3))}
    assert all(a==b for a,b in r['monic_irreducible_prime_degree_counts'].values())
    r['norm_one_multiplication_eigenvalues_lambda_lambda_inverse']={p:eigen_mult_by_norm_one(p)for p in(3,5,7)};assert all(r['norm_one_multiplication_eigenvalues_lambda_lambda_inverse'].values())
    r['augmentation_pth_power_zero_in_k[(Z/p)^2]']={p:augmentation_pth_power_zero(p)for p in(2,3,5)};assert all(r['augmentation_pth_power_zero_in_k[(Z/p)^2]'].values())
    hb={}
    for e,g in((6*5,7),(6*7,6*5),(6*11,2),(6*13,30),(12,1),(18,18)):
        c=hilbert_coeffs(e,g,4000);hb[f'e={e},g={g}']={'max_coeff':max(c),'min_coeff':min(c),'max_after_e+g':max(c[e+g:]),'tail_values_degree_3700_to_4000':sorted(set(c[3700:]))}
        assert min(c)>=0 and max(c[e+g:])<=max(c)
    r['hilbert_series_bounded_coefficients']=hb
    r['pth_power_ideal_weight_bound_5(T-1)']={T:monomial_count_weighted(T)for T in(3,5,9,27)};assert all(r['pth_power_ideal_weight_bound_5(T-1)'].values())
    p,M=smallest_operator_prime();r['smallest_prime_with_odd_M_satisfying_operator_hypotheses']={'p':p,'M':M,'16M^2':16*M*M,'(2floor(M/8))^3':(2*(M//8))**3,'beta':__import__('math').log(2*(M//8),p),'D=2(p-1)>12':2*(p-1)>12}
    assert 16*M*M<p<(2*(M//8))**3 and M%2==1 and M>=81 and r['smallest_prime_with_odd_M_satisfying_operator_hypotheses']['beta']>1/3
    # symbol parity: P(-A,-B,-C)=P(A,B,C) for P=sum c_h C^(2h)(AB)^(3(d-h)) since every term has even total degree 6d and even C-degree.
    r['symbol_fixed_by_sign_involution']=all((6*d)%2==0 and all((2*hh)%2==0 and(3*(d-hh)*2)%2==0 for hh in range(d+1))for d in(5,7,11))
    # A-adic valuation of alpha A^3 B^3 is odd (3), so C^2-alpha A^3B^3 is Eisenstein-irreducible over kbar(B)[A][C] in C: finite check that 3 is odd and that 2 does not divide 3.
    r['odd_A_valuation_of_cubic_term']=(3%2==1)
    return r

def main():
    anchors=read(A/'ANCHORS.json');assert anchors['file_count']==73 and anchors['sha256']=={'FINAL.md':FINAL,'MANIFEST.json':MANIFEST,'REPORT.md':REPORT}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors['sha256'].items())
    run=verifier(A,FINAL,MANIFEST,REPORT);assert run.returncode==0 and not run.stderr and clean(run.stdout).strip()=='Artifact bytes and exact selection verified: 73 files. No mathematical verdict.',run
    m=read(A/'MANIFEST.json');assert m['excluded_root_files']==['ANCHORS.json','MANIFEST.json','REPORT.md']and m['excluded_subtrees']==['private-controls/']and len(m['files'])==73 and sum(x['bytes']for x in m['files'])==9077473;names={x['path']for x in m['files']}
    for x in m['files']:p=A/x['path'];assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']
    rootfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};ctrl={f for f in rootfiles if f.startswith('private-controls/')};assert ctrl=={'private-controls/FINAL.md','private-controls/MANIFEST.json','private-controls/REPORT.md','private-controls/sample.txt'}and rootfiles==names|{'MANIFEST.json','REPORT.md','ANCHORS.json'}|ctrl and len(rootfiles)==80
    assert {'FINAL.md','FROZEN.md','AUTHOR-PROOF.md','PREFREEZE.md','INTERFACES.md','verify_packet.py','private-controls-run.py','private/READING-LIMITS.md','private/policy.json','private/policy-comparison.txt','private/source-authentication.json','private/family-tree.json','private/freeze.json','private/control-results.json','private/reading-extents.json','private/late-reads.json','private/history-reading.json','private/history-reading-additional.json','private/history-navigation.json','private/history-navigation-supplement.json','private/source319-catalogue.txt'}<=names
    assert not any(p.is_symlink()for p in A.rglob('*'))
    # frozen statement and chronology
    fz=read(V/'freeze.json');assert fz['file']=='FROZEN.md'and fz['sha256']==FROZEN==sha(A/'FROZEN.md')and fz['bytes']==2265==(A/'FROZEN.md').stat().st_size
    tf=datetime.datetime.fromisoformat(fz['time_utc']);tm=datetime.datetime.fromisoformat(m['created_utc']);assert tf<tm
    mt={x['path']:x for x in m['files']};assert mt['FROZEN.md']['sha256']==FROZEN and mt['AUTHOR-PROOF.md']['sha256']==sha(A/'AUTHOR-PROOF.md')and mt['AUTHOR-PROOF.md']['bytes']==34147
    ap=(A/'AUTHOR-PROOF.md').read_text();assert FROZEN in ap and FROZEN in(A/'FINAL.md').read_text()and FROZEN in(A/'REPORT.md').read_text()
    # pinned tree, canonical blobs exhausting the folder, wrapper and include order
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    auth=read(V/'source-authentication.json');assert len(auth)==12
    for x in auth:
        e=lookup[x['path']];p=A/x['local'];d=p.read_bytes();assert x['path'].startswith(FOLDER)and e['type']=='blob'and len(d)==x['bytes']==e['size']and x['git_blob']==e['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()and sha(p)==x['sha256']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    authpaths=sorted(x['path']for x in auth);famblobs=sorted(k for k,e in lookup.items()if k.startswith(FOLDER)and e['type']=='blob');fament=[k for k in lookup if k.startswith(FOLDER)]
    assert famblobs==authpaths and len(fament)==14
    ft=read(V/'family-tree.json');assert sorted(e['path']for e in ft)==sorted(fament)and all(lookup[e['path']]['sha']==e['sha']and lookup[e['path']].get('size')==e.get('size')for e in ft)
    assert lookup[FOLDER+WRAPPER[0]]['size']==WRAPPER[1]and lookup[FOLDER+WRAPPER[0]]['sha']==WRAPPER[2]
    wb=(V/'source/build/main.tex').read_bytes();ins=re.findall(rb'\\(input|include|bibliography)\{([^}]*)\}',wb)
    assert [t.decode()for _,t in ins]==['sections/'+s for s in SECTIONS]+['references']and all(k==b'input'for k,_ in ins)
    for s in SECTIONS+['../references']:
        t=(V/'source/build/sections'/(s+'.tex')).resolve();assert t.is_file()and not re.findall(rb'\\(input|include)\{',t.read_bytes()),s
    textblobs=[x for x in auth if not x['path'].endswith('.pdf')];assert len(textblobs)==11 and sum(1 for x in auth if x['path'].endswith('.pdf'))==1
    for x in textblobs:(A/x['local']).read_bytes().decode('utf-8')
    rl=(V/'READING-LIMITS.md').read_text()
    for x in textblobs:assert f'[0,{x["bytes"]})'in rl,x['path']
    # late source rereads lie inside the files and agree between the two records
    rx=read(V/'reading-extents.json');lr=read(V/'late-reads.json');assert rx['late_source_rereads']==lr and len(lr)==4 and lr[3]['file']=='AGENTS.md'
    for x in lr[:3]:s,e=x['bytes'];assert 0<=s<e<=(A/x['file']).stat().st_size and x['kind'].startswith('post-freeze reread')
    # direct reads, catalogue span, completed copies, history spans
    cat=span(P/'sources/CONTENTS.md',544391,545514);assert (V/'source319-catalogue.txt').read_bytes()==cat and hashlib.sha256(cat).hexdigest()=='96ee44bd172daac534d5655e2d9c88fa010e099d917c59878e0bc78a22705a97'and cat.startswith(b'**319. ')and b'lean/docs/'not in cat
    ce=[('discovery-structural-r194-parent/assessment.md',10628,'a389a0fb63cf48b0e39c0ce8654ac0e10b9b8ac4a8da5882b65e4f121b98411c'),('fresh-structural-discovery-r194/FINAL.md',3101,None),('fresh-structural-discovery-r194/INTERFACES.md',18605,None),('fresh-structural-discovery-r194/DERIVATIONS.md',24014,None),('fresh-structural-discovery-r194/COMPARISON.md',3680,None),('fresh-structural-discovery-r194/private/READING-LIMITS.md',13066,None)]
    for rel,nb,hx in ce:
        o=B/rel;c=V/'completed-exceptions'/rel;assert o.stat().st_size==nb and c.read_bytes()==o.read_bytes()and(hx is None or sha(o)==hx)
    assert len(list((V/'completed-exceptions').rglob('*')))==len([p for p in(V/'completed-exceptions').rglob('*')if p.is_dir()])+6
    hr=read(V/'history-reading.json');assert len(hr)==2
    for x in hr:s,e=x['extent'];d=span(P/x['path'],s,e);assert hashlib.sha256(d).hexdigest()==x['sha256']and d.startswith(x['heading'].encode())
    assert (V/'history-i105-chromatic-homotopy-discovery.md').read_bytes()==span(P/hr[0]['path'],*hr[0]['extent'])and(V/'history-i107-rational-tail-attachment.md').read_bytes()==span(P/hr[1]['path'],*hr[1]['extent'])
    ha=read(V/'history-reading-additional.json');assert len(ha)==7 and [x['copy']for x in ha]==[f'history-additional-{i}.md'for i in range(7)]
    for x in ha:d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and(V/x['copy']).read_bytes()==d and d.startswith(x['heading'].encode())
    r39=[x for x in ha if x['path'].endswith('308-positive-transfer.md')];assert [(x['start'],x['end'])for x in r39]==[(953,2590),(2590,4051),(4051,6297),(6297,7763)]and(P/r39[0]['path']).stat().st_size==7763
    assert [(x['start'],x['end'])for x in ha if 'i107'in x['path']]==[(13497,15450),(31276,34401),(34401,37109)]
    # every history extent ends at the next equal/higher heading or EOF
    for pth,s,e in[(x['path'],*x['extent'])for x in hr]+[(x['path'],x['start'],x['end'])for x in ha]:
        f=P/pth;sz=f.stat().st_size;lvl=len(span(f,s,min(e,s+8)).split(b' ')[0])
        if e<sz:nxt=span(f,e,min(sz,e+8));assert nxt.startswith(b'#')and len(nxt.split(b' ')[0])<=lvl,(pth,s,e)
    nav=read(V/'history-navigation.json');assert len(nav['eligible'])==1692 and len(nav['nonutf8'])==12 and len(nav['hits'])==11 and set(nav['queries'])=={'hahn_wilson','bp_generation','operation','local','primitive'}
    sup=read(V/'history-navigation-supplement.json');assert len(sup)==109
    FORBID=('r162','owner-recovery','arithmetic162','r156','r193','r194','structural195','fresh-structural-discovery-r195','k369','t185','r160','r161')
    for x in nav['hits']+nav['eligible']+sup:assert not any(t in x['path'].casefold()for t in FORBID),x['path']
    for x in nav['eligible']:assert (P/x['path']).stat().st_size==x['bytes']
    for x in nav['hits']:assert sha(P/x['path'])==x['sha256']
    assert {hh['path']for hh in nav['hits']}>={'frontier/iterations/i105-chromatic-homotopy-discovery.md','frontier/iterations/i107-rational-tail-attachment.md'}
    # primary PDFs, extractions, page extents and renders
    rc=[];fails=[]
    for f in('primary/receipts.json','primary/receipts-additional.json','primary/final-access.json'):
        for x in read(V/f):(fails if 'failure'in x else rc).append(x)
    for l in(V/'primary/additional-access.jsonl').read_text().splitlines():
        x=json.loads(l);(fails if 'failure'in x else rc).append(x)
    assert sorted(x['name']for x in rc)==['Barkan-v2','Bhargava-original','Bhargava2000','Christensen2013','HW2022','LP2026','MR1999','Pstragowski-v2']and sorted(x['name']for x in fails)==['AVVO-JSTOR','AVVO-alt','AVVO1989']
    for x in rc:
        pdf=V/'primary'/(x['name']+'.pdf');assert pdf.stat().st_size==x['bytes']and sha(pdf)==x['sha256']and pdf.read_bytes()[:5]==b'%PDF-'
        if 'text_sha256'in x:assert sha(V/'primary'/(x['name']+'.txt'))==x['text_sha256']
    pages={}
    for e in rx['primary']:
        t=A/e['file'];b=t.read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'];ff=[-1]+[i for i,c in enumerate(b)if c==12]
        for pe in e['read_page_extents']:
            s,en=pe['start'],pe['end'];pg=pe['page'];assert 0<=s<en<=len(b)and s==ff[pg-1]+1 and b[en:en+1]in(b'\x0c',b'')and ff[pg]==en if pg<len(ff)else True,(e['file'],pg)
        pages[Path(e['file']).stem]=(sorted(pe['page']for pe in e['read_page_extents']),sorted(pe['page']for pe in e['read_page_extents']if pe.get('late')))
    assert pages['LP2026'][0]==list(range(1,29))and pages['MR1999'][0]==[4,5,6,15,16]and pages['Christensen2013'][0]==[9,10,11,12,13,41,42,43,44]and pages['Pstragowski-v2'][0]==[18,19,22,23,24]and pages['Barkan-v2'][0]==[2,27]and pages['Bhargava-original'][0]==list(range(4,16))and pages['HW2022'][0]==list(range(1,9))
    assert 'Bhargava2000'not in pages
    renders=sorted(p.name for p in(V/'primary').glob('*.png'));assert renders==['Christensen2013-page11.png','Pstragowski-v2-page19.png']and all((V/'primary'/n).read_bytes()[:8]==b'\x89PNG\r\n\x1a\n'for n in renders)
    # guards and the pre-traversal policy comparison required by the brief
    pol=read(V/'policy.json');W=set(pol['wildcards']);L=set(pol['literal_wildcards']);Tw=set(pol['no_r_twins'])
    assert len(L)==169 and len(Tw)==169 and len(W)==339 and len(set(pol['substrings']))==150 and L<=W and Tw<=W and pol['own_root']=='frontier/campaigns/2026-10-14/fresh-structural-discovery-r195'and {'publication','check'}<=set(pol['substrings'])
    assert {'*k369r134-*','*t185r144-*','*owner-recovery*','*s176a*','*arithmetic*r162*','*arithmetic*r156*','*structural*r194*','*structural*r195*','*structural*r203*','*analytic*r195*','*arithmetic*r168*'}<=L
    for w in L:
        tw=re.sub(r'\*r(\d+)',r'*\1',w,count=1)if re.search(r'\*r\d',w)else re.sub(r'r(\d{3}-)',r'\1',w,count=1)
        assert tw==w or tw in W,(w,tw)
    pc=(V/'policy-comparison.txt').read_text();assert pc.startswith('BEFORE FIRST TRAVERSAL: all 169 literal wildcard guards and all 169 no-r twins individually installed and compared.')and pc.count('INSTALLED')>=169 and '*k369r134-*'in pc and '*t185r144-*'in pc and 'MISSING'not in pc
    brief=B/'expanded-target-2026-10-17/fresh-structural-r195-brief.txt';assert sha(brief)=='cbfb27ed482699bda9d27006d1fcd92b806dc90e3ab9772fe8115968f04dc067'and brief.stat().st_size==29599 and 'cbfb27ed482699bda9d27006d1fcd92b806dc90e3ab9772fe8115968f04dc067'in rl
    briefw=set(re.findall(r'\*[a-z0-9*\-]+\*',brief.read_text()));assert briefw<=W,briefw-W
    # controls: recorded results, then rerun on temporary copies of the child's fixture and of the actual packet
    ctl=read(V/'control-results.json');assert ctl['results']==['unchanged tiny control accepted','sample.txt copied corruption rejected','FINAL.md copied corruption rejected','MANIFEST.json copied corruption rejected','REPORT.md copied corruption rejected','extra copied file rejected']
    pcd=A/'private-controls';assert (pcd/'FINAL.md').read_bytes()==(A/'FINAL.md').read_bytes()and(pcd/'REPORT.md').read_bytes()==(A/'FROZEN.md').read_bytes()==(pcd/'sample.txt').read_bytes()
    ca={n:sha(pcd/n)for n in('FINAL.md','MANIFEST.json','REPORT.md')};good=verifier(pcd,ca['FINAL.md'],ca['MANIFEST.json'],ca['REPORT.md']);assert good.returncode==0 and clean(good.stdout).strip()=='Artifact bytes and exact selection verified: 2 files. No mathematical verdict.'
    controls_rerun=1
    with tempfile.TemporaryDirectory()as td:
        for n in('sample.txt','FINAL.md','MANIFEST.json','REPORT.md'):
            t=Path(td)/'fx';shutil.copytree(pcd,t);(t/n).write_bytes((t/n).read_bytes()+b'!');r=verifier(t,ca['FINAL.md'],ca['MANIFEST.json'],ca['REPORT.md']);assert r.returncode!=0 and('mismatch'in r.stderr or 'JSONDecodeError'in r.stderr or 'Expecting'in r.stderr),(n,r.stderr[-200:]);shutil.rmtree(t);controls_rerun+=1
        t=Path(td)/'fx';shutil.copytree(pcd,t);(t/'extra.txt').write_bytes(b'extra\n');r=verifier(t,ca['FINAL.md'],ca['MANIFEST.json'],ca['REPORT.md']);assert r.returncode!=0 and 'Selection mismatch'in r.stderr;shutil.rmtree(t);controls_rerun+=1
        # parent cases on a temporary copy of the ACTUAL packet
        t=Path(td)/'pk';shutil.copytree(A,t);r=verifier(t,FINAL,MANIFEST,REPORT);assert r.returncode==0
        (t/'private/unlisted.txt').write_bytes(b'x');r=verifier(t,FINAL,MANIFEST,REPORT);assert r.returncode!=0 and 'Selection mismatch'in r.stderr and 'private/unlisted.txt'in r.stderr;(t/'private/unlisted.txt').unlink();controls_rerun+=1
        (t/'PREFREEZE.md').unlink();r=verifier(t,FINAL,MANIFEST,REPORT);assert r.returncode!=0 and 'Nonregular or missing selected file: PREFREEZE.md'in r.stderr;shutil.copy2(A/'PREFREEZE.md',t/'PREFREEZE.md');controls_rerun+=1
        fb=(t/'FROZEN.md').read_bytes();(t/'FROZEN.md').write_bytes(fb+b'\n');r=verifier(t,FINAL,MANIFEST,REPORT);assert r.returncode!=0 and 'Selected file mismatch: FROZEN.md'in r.stderr;(t/'FROZEN.md').write_bytes(fb);controls_rerun+=1
        (t/'FINAL.md').write_bytes((t/'FINAL.md').read_bytes()+b'\n');r=verifier(t,FINAL,MANIFEST,REPORT);assert r.returncode!=0 and 'Detached anchor mismatch: FINAL.md'in r.stderr;controls_rerun+=1
        r=verifier(A,FINAL,MANIFEST,'0'*64);assert r.returncode!=0 and 'Detached anchor mismatch: REPORT.md'in r.stderr;controls_rerun+=1
    # --- Parent finite rechecks of the retained bookkeeping (not gates) ---
    rechecks=parent_rechecks()
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors['sha256'],'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':clean(run.stdout).strip(),'selected_files':73,'selected_bytes':9077473,'root_files':80,'detached_carriers':3,'control_files':4,'frozen':{'sha256':FROZEN,'bytes':2265,'time_utc':fz['time_utc'],'manifest_created_utc':m['created_utc'],'frozen_before_seal':True,'author_proof_sha256':mt['AUTHOR-PROOF.md']['sha256'],'author_proof_bytes':34147},'canonical_objects':12,'canonical_folders':1,'tree_entries_in_folder':14,'canonical_folder_exhausted':True,'wrapper_anchor':{'path':FOLDER+WRAPPER[0],'bytes':WRAPPER[1],'git_blob':WRAPPER[2]},'wrapper_inputs_in_order':['sections/'+s for s in SECTIONS]+['references'],'nested_inputs_in_sections':0,'source_text_objects_fully_read_author_claim':11,'source_pdfs_authenticated_only':1,'late_source_rereads':3,'direct_reads':['AGENTS.md','sources/upstream.json','NEW-TEN[4801,6347)'],'catalogue_extent_copied':[544391,545514],'completed_exception_copies_verified':6,'history_extents':9,'history_extents_heading_bounded':True,'history_eligible_utf8':1692,'navigation_hits':11,'navigation_supplement_hits':109,'primary_pdfs':8,'primary_semantically_read':7,'primary_rejected_false_attribution':['Bhargava2000 (course exposition)'],'primary_fetch_failures':[{'name':x['name'],'url':x['url'],'failure':x['failure']}for x in fails],'primary_pages':{k:v[0]for k,v in pages.items()},'primary_late_pages':{k:v[1]for k,v in pages.items()if v[1]},'renders_inspected':renders,'controls_rerun':controls_rerun,'guards':{'literal_wildcards':169,'no_r_twins':169,'wildcards':339,'substrings':150,'brief_wildcards_all_installed':True,'pretraversal_comparison_recorded':True},'parent_exact_rechecks':rechecks,'parent_recheck_description':'Finite bookkeeping rechecks independent of the child text: brute-force counts of monic irreducibles of prime degree d over F_{p^2} against (q^d-q)/d for q=9,25 and d=2,3; multiplication by a norm-one element of F_{p^2} has F_p-eigenvalues lambda and lambda^p=lambda^-1 (p=3,5,7); p-th powers of augmentation elements vanish in F_p[(Z/p)^2] on random elements (p=2,3,5); the Hilbert series (1-z^e)(1-z^g)/((1-z)^2(1-z^3)) has bounded nonnegative coefficients to degree 4000 for several (e,g); monomials below the T-th powers of A,B,C have weight at most 5(T-1); the frozen operator hypotheses are nonvacuous with the smallest admissible prime and odd M recorded (beta>1/3, D>12); the symbol P_j is fixed by the sign involution. These are not a proof review of the author argument (operator initialization for b_j, microlocal flatness at a non-coordinate prime, the enlarged dual-ghost target class, relative descent with Galois conjugates), which is reserved to the independent reviews.','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, FROZEN, AUTHOR-PROOF (all eight sections), PREFREEZE, INTERFACES, REPORT, ANCHORS, verify_packet.py, private-controls-run.py, private/READING-LIMITS.md and the private record schemas (source-authentication, family-tree, freeze, reading-extents, late-reads, history-reading(+additional), history-navigation(+supplement), policy, policy-comparison, primary receipts/access, control-results, history_select.py). Source319 (11 text objects) and primary (LP 2026 final, MR 1999, Christensen 2013, Pstragowski v2, Barkan v2, Bhargava 2000 original, HW v5) operative reading is attributed to the child, not fresh parent protected-body reading. Live Arithmetic162d (other parent thread) not inspected.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['selected_files','root_files','canonical_objects','completed_exception_copies_verified','history_extents','primary_pdfs','controls_rerun','parent_exact_rechecks','entire_root_unchanged','artifact_only']},default=str))
if __name__=='__main__':main()
