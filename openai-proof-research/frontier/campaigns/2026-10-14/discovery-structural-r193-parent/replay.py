#!/usr/bin/env python3
"""Read-only Structural193 discovery intake; artifact checks and finite rechecks only, no mathematical gate."""
import collections,datetime,hashlib,importlib.util,itertools,json,random,re,shutil,stat,subprocess,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r193';V=A/'private'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
FOLDER='preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/'
def read(p):return json.loads(p.read_bytes())
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
ENV={'PYTHON_COLORS':'0','PATH':'/usr/bin:/bin'}
def verifier(root,F,M,R):
    return subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),str(root),'--final-sha256',F,'--manifest-sha256',M,'--report-sha256',R],cwd=P,capture_output=True,text=True,env=ENV)
def clean(s):return re.sub(r'\x1b\[[0-9;]*m','',s)

# ---------------- parent model: normalized chains of poset nerves, relative to a downward-closed A ----------------
# Chains are dicts {tuple-of-vertices (strictly increasing in the poset order): int}. Independent of the child's categorical model.
def add(*terms):
    out=collections.defaultdict(int)
    for c,ch in terms:
        for s,v in ch.items():out[s]+=c*v
    return {s:v for s,v in out.items()if v}
def lin(f,ch):return add(*[(v,f(s))for s,v in ch.items()])
def norm1(ch):return sum(abs(v)for v in ch.values())
class PosetNerve:
    def __init__(s,elems,le,A):
        s.E=list(elems);s.le=le;s.A=set(A);assert all(a in s.A for a in s.E for b in s.E if b in s.A and le(a,b)) # A downward closed
    def nondeg(s,chain):return {} if len(set(chain))<len(chain) else {tuple(chain):1}
    def rel(s,ch):return {c:v for c,v in ch.items()if not set(c)<=s.A}
    def d(s,ch):
        out={}
        for c,v in ch.items():
            for i in range(len(c)):out=add((1,out),(v*(-1)**i,{c[:i]+c[i+1:]:1}))if len(c)>1 else out
        return s.rel(out)
    def simplices(s,q,sub=None):
        els=[e for e in s.E if sub is None or e in sub]
        return [c for c in itertools.combinations(els,q+1)if all(s.le(c[i],c[i+1])and c[i]!=c[i+1]for i in range(q))and not set(c)<=s.A]
    def prism(s,F,G,c):# F<=G pointwise poset maps; normalized prism operator (2)
        out={}
        for i in range(len(c)):
            out=add((1,out),((-1)**i,s.nondeg(tuple(F[v]for v in c[:i+1])+tuple(G[v]for v in c[i:]))))
        return s.rel(out)
    def h_rec(s,new,r,c):# the overlap-corrected recursion (3)-(6) on the relative complex of E=A∪new
        if set(c)<=s.A or not set(c)<=s.A|set(new):return {}
        maxima=[x for x in new if not any(x!=y and s.le(x,y)for y in new)]
        Enew=set(new)
        if len(maxima)==1:
            x=maxima[0];t=r[x];F={e:e for e in s.E};G={e:(x if e in Enew else e)for e in s.E};K={e:(t if e in Enew else e)for e in s.E}
            return add((1,s.prism(K,G,c)),(-1,s.prism(F,G,c)))
        x1,x2=sorted(maxima)[:2];n1=[x for x in new if x!=x1];n2=[x for x in new if x!=x2];n12=[x for x in new if x not in(x1,x2)]
        # section s: piece 1 whenever possible (piece membership: all new vertices in E_i); t: minus the piece-2 coefficient of intersection simplices
        in1=x1 not in c
        if in1:
            return s.h_rec(n1,r,c)  # s'(c) has no correction: alpha = t d s (c) and t kills piece-1 chains... except its intersection part; handled below
        # c lies in piece 2 only (contains x1... wait: contains x1 means not in E_1 piece => piece 2 is E_2 = E\{x2}); c must then avoid x2
        assert x2 not in c
        dc=s.d({c:1});alpha={z:-v for z,v in dc.items()if x1 not in z and x2 not in z}  # t(d_B s c) = minus piece-2 coefficients of intersection faces
        corr=lin(lambda z:s.h_rec(n12,r,z),alpha)  # h_A alpha
        # s' = s - i h_A alpha, i(z)=(z,-z); h_B=(h1,h2); q=sum
        return add((1,s.h_rec(n2,r,c)),(-1,lin(lambda z:s.h_rec(n1,r,z),corr)),(1,lin(lambda z:s.h_rec(n2,r,z),corr)))
def random_retract_poset(rng,na,nn):
    # ground set: A = 0..na-1 (a chain, so every new element has a greatest lower bound in A), new = na..na+nn-1 with random order among new and random A-lower-bounds
    E=list(range(na+nn));A=list(range(na));below={}
    for x in range(na,na+nn):below[x]=set(rng.sample(range(na,x),rng.randint(0,min(2,x-na))))
    # transitive closure among new
    changed=True
    while changed:
        changed=False
        for x in range(na,na+nn):
            for y in list(below[x]):
                if not below[y]<=below[x]:below[x]|=below[y];changed=True
    r={}
    for x in range(na,na+nn):
        lower=rng.randint(0,na-1);r[x]=max([lower]+[r[y]for y in below[x]])
    def le(u,v):
        if u==v:return True
        if u<na and v<na:return u<=v
        if u<na:return u<=r[v]
        if v<na:return False
        return u in below[v]
    return E,A,r,le
def parent_rechecks():
    rng=random.Random(20261022);checked=0;norm_ok=0
    for trial in range(60):
        na=rng.randint(1,3);nn=rng.randint(1,5);E,A,r,le=random_retract_poset(rng,na,nn);N=PosetNerve(E,le,A);new=[e for e in E if e not in A]
        # retraction r is the right adjoint: r(x) in A, r(x)<=x, and a<=x iff a<=r(x) for a in A
        for x in new:assert le(r[x],x)and all((le(a,x))==(a<=r[x])for a in A)
        H=lambda c:N.h_rec(new,r,c)
        maxq=len(E)-1
        for q in range(maxq+1):
            for c in N.simplices(q):
                assert not N.d(N.d({c:1}))
                lhs=add((1,N.d(H(c))),(1,lin(H,N.d({c:1}))));assert lhs=={c:1},(E,A,r,c,lhs)  # dh+hd=id on relative chains (7)
                hb=lin(H,N.d(H(c)))  # h^flat = h d h
                assert add((1,N.d(hb)),(1,lin(lambda z:lin(H,N.d(H(z))),N.d({c:1}))))=={c:1}and not lin(lambda z:lin(H,N.d(H(z))),hb)  # square-zero normalization contracts and squares to zero
                checked+=1
        # chain-norm recurrence (8): B_m(q) bounds ||h_q||_1 with m=|new|
        def Bm(m,q):
            if q<0 or m==0:return 0
            if m==1:return 2*(q+1)
            return max(2*(q+1),Bm(m-1,q)*(1+2*(q+1)*Bm(m-2,q-1)))
        for q in range(maxq+1):
            for c in N.simplices(q):assert norm1(H(c))<=Bm(len(new),q);norm_ok+=1
    # (12): for any operators with dh+hd=id, ∂(h z)=z-h∂z, where ∂z=dz-(-1)^k z d  -- checked on a random finite complex with random z
    rng2=random.Random(7);E,A,r,le=random_retract_poset(rng2,2,4);N=PosetNerve(E,le,A);new=[e for e in E if e not in A];H=lambda c:N.h_rec(new,r,c)
    basis={q:N.simplices(q)for q in range(len(E))}
    for k in(0,1,2):
        table={c:{z:rng2.randint(-2,2)for z in basis.get(len(c)-1+k,[])}for q in basis for c in basis[q]}
        z=lambda c:{s:v for s,v in table[c].items()if v};sgn=(-1)**k
        for q in basis:
            for c in basis[q]:
                dz=lambda c:add((1,N.d(z(c))),(-sgn,lin(z,N.d({c:1}))))  # ∂z
                lhs=add((1,N.d(lin(H,z(c)))),(-(-1)**(k+1),lin(lambda y:lin(H,z(y)),N.d({c:1}))))  # ∂(h z), degree k+1
                rhs=add((1,z(c)),(-1,lin(H,dz(c))))
                assert lhs==rhs
    # (15): finite perturbation contraction of the simplicial replacement of a two-stage inclusion C_F0 -> C_F1 (strict chain F0⊊F1), with h0=(-1)^p h_{F_p}
    E,A,r,le=random_retract_poset(random.Random(3),2,4);N=PosetNerve(E,le,A);new=[e for e in E if e not in A]
    F1=new;F0=new[:1];assert len(new)>=2  # any subset containing A is ir-stable since ir lands in A; F0 is a proper subset so F0⊊F1 is a strict chain
    h0f=lambda c:N.h_rec(F0,r,c);h1f=lambda c:N.h_rec(F1,r,c)
    # total complex: bidegree p=0 summands C_{F0}, C_{F1} (single-stage chains), p=1 summand C_{F0} for the chain F0⊊F1; δ(F0⊊F1; c)=ι(c)-c  (first deletion applies C_F0→C_F1 i.e. the inclusion, second deletion keeps c in C_F0)
    def tot_d(x):# x: dict keyed by ('0',F,c) or ('1',c)
        out={}
        for key,v in x.items():
            if key[0]=='0':
                for s,w in N.d({key[2]:1}).items():out=add((1,out),(v*w,{('0',key[1],s):1}))
            else:
                c=key[1]
                for s,w in N.d({c:1}).items():out=add((1,out),(-v*w,{('1',s):1}))  # d_0=(-1)^p d
                out=add((1,out),(v,{('0','F1',c):1}),(-v,{('0','F0',c):1}))  # δ
        return out
    def h0(x):
        out={}
        for key,v in x.items():
            if key[0]=='0':
                hf=h1f if key[1]=='F1' else h0f
                for s,w in hf(key[2]).items():out=add((1,out),(v*w,{('0',key[1],s):1}))
            else:
                for s,w in h0f(key[1]).items():out=add((1,out),(-v*w,{('1',s):1}))
        return out
    def delta(x):
        out={}
        for key,v in x.items():
            if key[0]=='1':out=add((1,out),(v,{('0','F1',key[1]):1}),(-v,{('0','F0',key[1]):1}))
        return out
    def Htot(x):# sum_k (-1)^k h0 (δ h0)^k, finite since δ lowers p
        out={};term=x;k=0
        while term:
            out=add((1,out),((-1)**k,h0(term)));term=delta(h0(term));k+=1
        return out
    basis0=[('0','F0',c)for q in range(len(E))for c in N.simplices(q,set(A)|set(F0))]+[('0','F1',c)for q in range(len(E))for c in N.simplices(q)]+[('1',c)for q in range(len(E))for c in N.simplices(q,set(A)|set(F0))]
    for key in basis0:
        x={key:1};assert not tot_d(tot_d(x))
        assert add((1,tot_d(Htot(x))),(1,Htot(tot_d(x))))==x,key  # D H_tot + H_tot D = id on the simplicial replacement
    # (19)/§9: the diamond obstruction for one stationary RIGHT cylinder const_o -> id in dimension >=2: exhaustive over nonnegative integer chains with coefficients <=3
    # positive basis: vertices o,a,b,t; edges oa,ob,at,bt,ot; 2-simplices oat,obt. Need h_t: nonneg 1-chain with d h_t=[t]-[o]; h_[a,t], h_[b,t]: nonneg 2-chains with d h_[a,t]=h_t-[o,a]-[a,t] and d h_[b,t]=h_t-[o,b]-[b,t]   (18) with q=1 and h_a=[o,a], h_b=[o,b] forced
    edges=['oa','ob','at','bt','ot'];tris=['oat','obt']
    def bd1(ch):
        out=collections.defaultdict(int)
        for e,v in ch.items():out[e[1]]+=v;out[e[0]]-=v
        return {k:v for k,v in out.items()if v}
    def bd2(ch):
        out=collections.defaultdict(int)
        for tri,v in ch.items():
            for i,sgn in((0,1),(1,-1),(2,1)):e=tri[:i]+tri[i+1:];out[e]+=sgn*v
        return {k:v for k,v in out.items()if v}
    solutions=0;ht_candidates=0
    for coeffs in itertools.product(range(4),repeat=5):
        ht={e:c for e,c in zip(edges,coeffs)if c}
        if bd1(ht)!={'t':1,'o':-1}:continue
        ht_candidates+=1
        for c2 in itertools.product(range(4),repeat=2):
            hat={t:c for t,c in zip(tris,c2)if c}
            if bd2(hat)!=add((1,ht),(-1,{'oa':1,'at':1})):continue
            for c3 in itertools.product(range(4),repeat=2):
                hbt={t:c for t,c in zip(tris,c3)if c}
                if bd2(hbt)==add((1,ht),(-1,{'ob':1,'bt':1})):solutions+=1
    assert ht_candidates==3 and solutions==0  # exactly the three paths (19); no positive 2-chains satisfy both edge equations
    # §10 prepend contraction on a poset with least vertex o: dh+hd=id-const_o and h^2=0, on random posets with a least element (full nerve, A empty)
    for trial in range(20):
        rng3=random.Random(100+trial);n=rng3.randint(2,6);rel={(i,j)for i in range(n)for j in range(i+1,n)if rng3.random()<0.6}|{(0,j)for j in range(1,n)}
        changed=True
        while changed:
            changed=False
            for(i,j)in list(rel):
                for(k,l)in list(rel):
                    if j==k and(i,l)not in rel:rel.add((i,l));changed=True
        le3=lambda u,v:u==v or(u,v)in rel;N3=PosetNerve(range(n),le3,[])
        hp=lambda c:({(0,)+c:1}if c[0]!=0 else{})
        for q in range(n):
            for c in N3.simplices(q):
                lhs=add((1,N3.d(hp(c))),(1,lin(hp,N3.d({c:1}))));rhs=add((1,{c:1}),(-1,{(0,):1}if q==0 else{}))
                assert lhs==rhs and not lin(hp,hp(c))
    return {'overlap_recursion_simplices_checked':checked,'norm_bound_checks':norm_ok,'filler_identity_12':True,'perturbation_15_two_stage':True,'diamond_h_t_candidates':ht_candidates,'diamond_single_cylinder_solutions':solutions,'prepend_contraction_posets':20}

def main():
    anchors=read(A/'ANCHORS.json');assert anchors=={'FINAL.md':'74b31f08fba6bcb12266b723d93468a0abcede5f37f55d6fee4235b3e9b3584a','private/MANIFEST.json':'be6e5c5bbb41d33811b8b776088805427df1dfff37844cae4c982031442b25d7','REPORT.md':'2a3f3dc9f24157f69ea4a506a52afb58b6b55b2f82e60ead0f8d0cfa9da922ea'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    F,M,R=anchors['FINAL.md'],anchors['private/MANIFEST.json'],anchors['REPORT.md']
    run=verifier(A,F,M,R);assert run.returncode==0 and not run.stderr and json.loads(clean(run.stdout))=={'artifact_integrity':'verified','mathematical_verdict':None,'payload_bytes':10269462,'payload_files':94}
    m=read(V/'MANIFEST.json');assert m['schema']=='r193-exact-packet-v1'and len(m['files'])==94 and sum(x['bytes']for x in m['files'])==10269462;names={x['path']for x in m['files']}
    for x in m['files']:p=A/x['path'];assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']
    rootfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};assert rootfiles==names|{'private/MANIFEST.json','REPORT.md','ANCHORS.json'}and len(rootfiles)==97
    assert {'FINAL.md','DERIVATIONS.md','INTERFACES.md','COMPARISON.md','RESEARCH-NOTES.md','verify_packet.py','private/READING-LIMITS.md','private/brief.txt','private/policy.json','private/policy-comparison.json','private/chain_calculation.py'}<=names
    assert not any(p.is_symlink()for p in A.rglob('*'))
    # pinned tree, canonical blobs exhausting the folder, wrapper and include order
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    auth=read(V/'source-authentication.json');assert len(auth)==13
    for x in auth:
        e=lookup[x['path']];p=A/x['local'];d=p.read_bytes();assert x['path'].startswith(FOLDER)and e['type']=='blob'and len(d)==x['bytes']==e['size']and x['git_blob']==e['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()and sha(p)==x['sha256']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert sorted(k for k,e in lookup.items()if k.startswith(FOLDER)and e['type']=='blob')==sorted(x['path']for x in auth)and sum(1 for k in lookup if k.startswith(FOLDER))==15
    st=read(V/'source-tree.json');assert len(st)==15 and sorted((e['path'],e['sha'])for e in st)==sorted((k,e['sha'])for k,e in lookup.items()if k.startswith(FOLDER))
    assert lookup[FOLDER+'build/paper.tex']['size']==3804 and lookup[FOLDER+'build/paper.tex']['sha']=='8c9f165f64359998bbd84da06247fea5920225f4'and lookup[FOLDER+'paper.pdf']['size']==537399
    wb=(V/'source/build/paper.tex').read_bytes();ins=[(k,t)for k,t in re.findall(rb'\\(input|bibliography)\{([^}]*)\}',wb)]
    assert [t.decode()for _,t in ins]==['sections/01-introduction','sections/02-foundations','sections/03-relative-prisms','sections/04-labelled-pieces','sections/05-couniversality','sections/06-subdivided-attachments','sections/07-model-structure','sections/09-presentability','sections/08-method-context','references']
    ie=read(V/'include-edges.json');assert ie['nested_edges']==[]and len(ie['ordered_edges'])==10
    for (k,t),e in zip(ins,ie['ordered_edges']):
        s0,s1=e['wrapper_byte_extent'];cmd=wb[s0:s1];assert cmd.startswith(b'\\'+k)and t in cmd and e['kind']==k.decode()and(A/e['target']).is_file()and e['exists']
        assert e['target'].endswith(t.decode()+('.bib'if k==b'bibliography'else'.tex'))
    assert b'\\appendix'in wb and wb.index(b'\\appendix')<wb.index(b'sections/09-presentability')
    se=read(V/'source-extents.json');assert len(se)==13
    for x in se:
        p=A/x['local'];assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']
        if x['path'].endswith('.pdf'):assert x['semantic_extents']==[]and x['mode'].startswith('authentication only')
        else:assert x['semantic_extents']==[[0,x['bytes']]]and x['mode'].startswith('entire UTF8 text semantically read')
    for x in se:
        if not x['path'].endswith('.pdf'):p=A/x['local'];p.read_bytes().decode('utf-8')
    # direct reads, brief copy, catalogue span, completed copies, history spans
    assert (V/'brief.txt').read_bytes()==(B/'expanded-target-2026-10-17/fresh-structural-r193-brief.txt').read_bytes()and sha(V/'brief.txt')=='56362f41cf3324384eb7ab6a06e78494203b260a93ba74e5be2384a2c9933620'and(V/'brief.txt').stat().st_size==27772
    assert (V/'acceptance-bytes-4801-6347.txt').read_bytes()==span(P/'frontier/NEW-TEN-2026-10-14.md',4801,6347)
    assert (V/'direct-AGENTS.md').read_bytes()==(P/'AGENTS.md').read_bytes()and(V/'direct-upstream.json').read_bytes()==(P/'sources/upstream.json').read_bytes()
    cat=span(P/'sources/CONTENTS.md',539611,540867);assert (V/'source317-catalogue.txt').read_bytes()==cat and hashlib.sha256(cat).hexdigest()=='91568fbdee7b1ffead2fd2a53fb3dc634ae1f35e53e7b344c287352a0e5b586c'and cat.startswith(b'**317. ')
    ce=read(V/'completed-exceptions.json');assert len(ce)==6 and [x['path'][len('frontier/campaigns/2026-10-14/'):]for x in ce]==['discovery-structural-r192-parent/assessment.md','fresh-structural-discovery-r192/FINAL.md','fresh-structural-discovery-r192/INTERFACES.md','fresh-structural-discovery-r192/DERIVATIONS.md','fresh-structural-discovery-r192/COMPARISON.md','fresh-structural-discovery-r192/private/READING-LIMITS.md']
    for i,x in enumerate(ce):
        o=P/x['path'];assert o.stat().st_size==x['bytes']and sha(o)==x['sha256']and(V/f'completed-exception-{i}.txt').read_bytes()==o.read_bytes()
    assert ce[0]['sha256']=='8c2dbadd49d1af0f08f98b99f98df925c9a18d6fe6e25a611ce91d90fb339eb7'
    hx=read(V/'original-extents.json');assert len(hx)==6 and [(x['path'][len('frontier/campaigns/2026-10-14/'):],x['start'],x['end'])for x in hx]==[('fresh-structural-discovery-r41/equivariant-attachment-assessment.md',0,6260),('fresh-arithmetic-discovery-r34/slot-telescope.md',1274,3313),('fresh-arithmetic-discovery-r34/slot-telescope.md',0,424),('fresh-arithmetic-discovery-r34/slot-telescope.md',424,1274),('fresh-arithmetic-discovery-r34/slot-telescope.md',3313,5101),('fresh-arithmetic-discovery-r34/slot-telescope.md',5101,7129)]
    for x in hx:assert hashlib.sha256(span(P/x['path'],x['start'],x['end'])).hexdigest()==x['sha256']
    assert sum(1 for x in hx if x.get('late'))==5 and(V/'original-r41.txt').read_bytes()==(P/hx[0]['path']).read_bytes()and(V/'original-r34.txt').read_bytes()==(P/hx[1]['path']).read_bytes()and(V/'original-r34-section.txt').read_bytes()==span(P/hx[1]['path'],1274,3313)
    r34=(P/hx[1]['path']).read_bytes();assert r34[1274:1280]==b'## 2. 'or r34[1274:1277]==b'## '
    nav=read(V/'original-navigation.json');assert nav['counts']=={'pruned':6614,'non_utf8':12,'eligible':1692}and len(nav['decoded'])==1692 and len(nav['hits'])==52
    for x in nav['hits']+nav['decoded']:assert not any(t in x['path'].casefold()for t in('r160','r161','r192','r193','k369','t185','owner-recovery','fresh-structural-discovery-r191','fresh-arithmetic-discovery-r159'))
    for x in nav['decoded']:assert (P/x['path']).stat().st_size==x['bytes']
    cn=read(V/'original-complementary-navigation.json');assert len(cn)==4 and {x['path'][len('frontier/campaigns/2026-10-14/'):].split('/')[0]for x in cn}>={'fresh-arithmetic-discovery-r34','fresh-structural-discovery-r41'}
    # primary PDFs, extractions and page extents
    rc=read(V/'primary-receipts.json');assert [x['name']for x in rc]==['thomason1980','cisinski1999','gagna-v2','ara-maltsiniotis-2014-v3','ara-maltsiniotis-2020-v4','ara-maltsiniotis-2015-v1']and all('failure'not in x for x in rc)and rc[5]['late'].startswith('after DERIVATIONS initial version')
    for x in rc:
        pdf=V/'primary'/(x['name']+'.pdf');assert pdf.stat().st_size==x['bytes']and sha(pdf)==x['sha256']and(V/'primary'/(x['name']+'.txt')).stat().st_size>0 and x['extract_returncode']==0
    pe=read(V/'primary-extents.json');assert [x['name']for x in pe]==[x['name']for x in rc]and sum(len(x['extents'])for x in pe)==109
    for x in pe:
        tp=A/x['text_path'];assert tp.stat().st_size==x['text_bytes']and sha(tp)==x['text_sha256']
        for ex in x['extents']:assert hashlib.sha256(span(tp,ex['start'],ex['end'])).hexdigest()==ex['sha256']
    extra=0
    for f in('primary-extents-1.json','primary-extents-2.json','primary-extents-3.json'):
        for ex in read(V/f):assert hashlib.sha256(span(V/'primary'/(ex['name']+'.txt'),ex['start'],ex['end'])).hexdigest()==ex['sha256'];extra+=1
    assert extra==36 and len(list((V/'render').glob('*.png')))==11 and all(p.stat().st_size>0 for p in(V/'render').glob('*.png'))
    # guards and the pre-traversal policy comparison required by the brief
    pol=read(V/'policy.json');pc=read(V/'policy-comparison.json');W=set(pol['wildcards'])
    assert len(pol['wildcards'])==298 and len(pol['substrings'])==151 and pol['own_root']=='frontier/campaigns/2026-10-14/fresh-structural-discovery-r193'and 'publication'in pol['substrings']
    assert {'*k369r134-*','*t185r144-*','*arithmetic*r160*','*arithmetic*r161*','*arithmetic*r162*','*structural*r192*','*structural*r194*','*arithmetic*r156*','*arithmetic*r159*','*structural*r191*','*s176a*'}<=W
    assert pc['before_first_traversal']and pc['brief_sha256']=='56362f41cf3324384eb7ab6a06e78494203b260a93ba74e5be2384a2c9933620'and pc['missing']==[]and len(pc['guards'])==151 and all(g['both_installed']for g in pc['guards'])
    assert {g['literal']for g in pc['guards']}<=W and all(g['twin']in W for g in pc['guards'])and {'*k369r134-*','*t185r144-*'}<={g['literal']for g in pc['guards']}
    briefw=set(re.findall(r'\*[a-z0-9*\-]+\*',(V/'brief.txt').read_text()));assert briefw<=W,briefw-W
    # controls: recorded results, then rerun on temporary copies of the intact fixture
    ctl=read(V/'controls/control-results.json');assert ctl['originals_unchanged']and ctl['artifact_only']and [(c['case'],c['expected_exit'],c['actual_exit'])for c in ctl['cases']]==[('intact copied packet',0,0),('changed copied payload',1,1),('extra copied file',1,1),('wrong explicit anchor',1,1)]
    fx=V/'controls/good';fa=read(fx/'ANCHORS.json');assert all(sha(fx/p)==v for p,v in fa.items())and fa['FINAL.md']==F
    good=verifier(fx,fa['FINAL.md'],fa['private/MANIFEST.json'],fa['REPORT.md']);assert good.returncode==0 and json.loads(clean(good.stdout))==json.loads(ctl['cases'][0]['stdout'])
    with tempfile.TemporaryDirectory()as td:
        t=Path(td)/'fx';shutil.copytree(fx,t);(t/'RESEARCH-NOTES.md').write_bytes((fx/'RESEARCH-NOTES.md').read_bytes()+b'\n# tampered line\n');bad=verifier(t,fa['FINAL.md'],fa['private/MANIFEST.json'],fa['REPORT.md']);assert bad.returncode==1 and clean(bad.stderr).strip()==ctl['cases'][1]['stderr']
        shutil.rmtree(t);shutil.copytree(fx,t);(t/'unlisted.txt').write_bytes(b'x');ex=verifier(t,fa['FINAL.md'],fa['private/MANIFEST.json'],fa['REPORT.md']);assert ex.returncode==1 and clean(ex.stderr).strip()==ctl['cases'][2]['stderr']
        shutil.rmtree(t);shutil.copytree(fx,t);wrong=verifier(t,'0'*64,fa['private/MANIFEST.json'],fa['REPORT.md']);assert wrong.returncode==1 and clean(wrong.stderr).strip()==ctl['cases'][3]['stderr']
        shutil.rmtree(t);shutil.copytree(fx,t);(t/'RESEARCH-NOTES.md').unlink();mis=verifier(t,fa['FINAL.md'],fa['private/MANIFEST.json'],fa['REPORT.md']);assert mis.returncode==1 and 'missing' in clean(mis.stderr)
    assert (V/'controls/tampered/RESEARCH-NOTES.md').stat().st_size==2909 and(fx/'RESEARCH-NOTES.md').stat().st_size==2891 and(V/'controls/extra/unlisted.txt').is_file()
    # child chain calculation rerun on a temporary copy (its output path is project-relative; redirect to the temporary directory)
    with tempfile.TemporaryDirectory()as td:
        t=Path(td);src=(V/'chain_calculation.py').read_text();assert src.count("Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r193/private/chain-calculation.json')")==1
        (t/'chain_calculation.py').write_text(src.replace("Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r193/private/chain-calculation.json')","Path('chain-calculation.json')"))
        r=subprocess.run(['python','-I','-B',str(t/'chain_calculation.py')],cwd=td,capture_output=True,text=True,env=ENV,timeout=900);assert r.returncode==0,r.stderr
        cc=read(t/'chain-calculation.json');assert cc==read(V/'chain-calculation.json')
    assert [(x['degree'],x['simplices'],x['max_full_h_l1'])for x in cc['degrees']]==[(0,5,3),(1,13,4),(2,17,4),(3,17,4),(4,17,4),(5,17,4)]and len(cc['example']['h'])==4 and sorted(t['coefficient']for t in cc['example']['h'])==[-1,-1,1,1]and cc['not_a_general_proof']
    # --- Parent finite rechecks in an independent poset-nerve model (not gates) ---
    rechecks=parent_rechecks()
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':json.loads(clean(run.stdout)),'payload_files':94,'payload_bytes':10269462,'root_files':97,'detached_carriers':3,'canonical_objects':13,'canonical_folders':1,'blobs_per_folder':[13],'tree_entries_per_folder':[15],'canonical_folders_exhausted':True,'wrapper_anchor':{'path':FOLDER+'build/paper.tex','bytes':3804,'git_blob':'8c9f165f64359998bbd84da06247fea5920225f4'},'include_order_reparsed':[t.decode()for _,t in ins],'include_edge_extents_verified':10,'appendix_order':'09-presentability then 08-method-context (after \\appendix)','source_text_objects_fully_read':12,'source_pdfs_authenticated_only':1,'direct_reads':['AGENTS.md','sources/upstream.json','NEW-TEN[4801,6347)'],'catalogue_extent_copied':[539611,540867],'completed_exception_copies':6,'history_extents':6,'history_late_extents':5,'history_eligible_utf8':1692,'navigation_hits':[52,4],'primary_pdfs':6,'primary_fetch_failures':[],'primary_page_extents':[109,36],'primary_late':['ara-maltsiniotis-2015-v1 (after initial DERIVATIONS)','ara-maltsiniotis-2014-v3 pp.33-36 (after initial DERIVATIONS)'],'renders_inspected':11,'controls_rerun':4,'guards':{'wildcards':298,'substrings':151,'policy_comparison_guards':151,'missing':0,'brief_wildcards_all_installed':True},'child_calculations_rerun':['chain_calculation.py (86 nondegenerate simplices in degrees 0-5 of an actual n=1 pushout with identified old objects and idempotent arrow; identical chain-calculation.json)'],'parent_exact_rechecks':rechecks,'parent_recheck_description':'Independent poset-nerve model (ordinary nerve of E relative to the downward-closed A, X=U(A), right-adjoint retraction r): the overlap-corrected recursion (3)-(6) satisfies dh+hd=id on all relative nondegenerate simplices of 60 random retract-sieve posets (up to 5 new elements, all degrees); the square-zero normalization hdh contracts and squares to zero; the norm recurrence (8) bounds every computed l1 norm; the filler identity (12) holds for random operators of degree 0,1,2; the finite perturbation formula (15) contracts the simplicial replacement of a two-stage ir-stable inclusion; the diamond obstruction (§9) is exhaustive for nonnegative coefficients <=3 (exactly three h_t paths, zero solutions to both edge equations); the prepend contraction (§10) satisfies dh+hd=id-const_o and h^2=0 on 20 random posets with a least element. These are finite rechecks of the retained formulas, not a proof review of the unpaid positive realization.','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, ANCHORS, verify_packet.py, DERIVATIONS (all eleven sections), COMPARISON, READING-LIMITS excerpts and the private record schemas and chain_calculation.py. INTERFACES and RESEARCH-NOTES skimmed by structure only. Source317 (12 text objects) and primary (Thomason 1980, Cisinski 1999, Gagna, Ara-Maltsiniotis 2014/2015/2020) operative reading attributed to the child, not fresh parent protected-body reading. Live Arithmetic161/162 (other parent thread) not inspected.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['payload_files','root_files','canonical_objects','completed_exception_copies','history_extents','primary_pdfs','controls_rerun','parent_exact_rechecks','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
