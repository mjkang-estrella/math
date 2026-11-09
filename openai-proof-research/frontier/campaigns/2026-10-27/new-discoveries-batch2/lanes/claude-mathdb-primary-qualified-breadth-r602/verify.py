# Read-only independent verifier for lane claude-mathdb-primary-qualified-breadth-r602.
# Usage: python3 -B verify.py BATCHDIR [LANEDIR]   (LANEDIR defaults to BATCHDIR/lanes/claude-mathdb-primary-qualified-breadth-r602)
# Checks: lane manifest (hash/size, no extra files except manifest.json and final-receipt.json); flat bindings of originals;
# pinned r601/r603 manifests; r301 20 chunks + 8 frozen inputs in place; reservation/disjointness against current r603;
# each of the 50 records re-read at its chunk/line (line hash, canonical hash, exact statement); dispositions/proposals shape;
# exact recheck of the P1 graph certificate and the P2 K3 instance. Writes nothing. Exit 1 on any mismatch.
import hashlib,itertools,json,os,sys
from fractions import Fraction as F
B=os.path.realpath(sys.argv[1]); LN=os.path.join(B,'lanes')
ME=os.path.realpath(sys.argv[2]) if len(sys.argv)>2 else os.path.join(LN,'claude-mathdb-primary-qualified-breadth-r602')
def h(p):
    s=hashlib.sha256(); n=0
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): s.update(b); n+=len(b)
    return s.hexdigest(),n
J=lambda p:json.load(open(p,encoding='utf-8'))
errs=[]; rep={}
# 1. lane manifest
man=J(os.path.join(ME,'manifest.json')); L={e['path']:(e['sha256'],e['size']) for e in man['files']}
EXC={'manifest.json','final-receipt.json'}
if set(man['excluded_exact_paths'])!=EXC: errs.append('manifest exclusions')
for p,v in L.items():
    q=os.path.join(ME,p)
    if not os.path.isfile(q): errs.append('missing '+p)
    elif h(q)!=v: errs.append('hash/size mismatch '+p)
act=set()
for r,ds,fs in os.walk(ME):
    for f in fs: act.add(os.path.relpath(os.path.join(r,f),ME))
extra=sorted(act-set(L)-EXC)
if extra: errs.append('extra files %r'%extra)
if 'verify.py' not in L: errs.append('verifier not manifest-bound')
rep['manifest_files']=len(L)
def _checks():
    global errs
    # 2. flat bindings to originals
    FB=J(os.path.join(ME,'flat-bindings.json'))
    for e in FB:
        q=os.path.normpath(os.path.join(B,e['path']))
        if not os.path.isfile(q) or h(q)!=(e['sha256'],e['size']): errs.append('original '+e['path'])
    PIN={'lanes/root-mathdb-breadth-intake-r601/manifest.json':('fd199b647c5c807000277477af312eafe6182a53b8519c52653549cf9639f02f',16780),
         'lanes/root-mathdb-breadth-intake-r603/manifest.json':('a8261dc455e6b6438fe4714cab0af16a8b33581f671d6723d8e6c3740e137a90',9761),
         'lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json':('4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15',22047)}
    fbm={e['path']:(e['sha256'],e['size']) for e in FB}
    for p,v in PIN.items():
        if fbm.get(p)!=v: errs.append('pin '+p)
    m301=J(os.path.join(LN,'pi-mathdb-full-corpus-inventory-r301/manifest.json'))
    chunks=[e for e in m301['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
    for e in chunks+m301['frozen_inputs']:
        if fbm.get('lanes/pi-mathdb-full-corpus-inventory-r301/'+e['path'])!=(e['sha256'],e['bytes']): errs.append('r301 '+e['path'])
    if len(chunks)!=20 or len(m301['frozen_inputs'])!=8: errs.append('r301 counts')
    rep['flat_bindings']=len(FB); rep['r301_chunks']=len(chunks); rep['r301_frozen_inputs']=len(m301['frozen_inputs'])
    # 3. reservation and disjointness
    rs=J(os.path.join(LN,'root-mathdb-breadth-intake-r601/reserved-ids.json')); ids=rs['ids']; S=set(ids)
    q=J(os.path.join(LN,'root-mathdb-breadth-intake-r601/queue.json'))
    if [r['mathdb_id'] for r in q]!=ids or len(S)!=50 or rs['lane']!='claude-mathdb-primary-qualified-breadth-r602': errs.append('assignment')
    act3=J(os.path.join(LN,'root-mathdb-breadth-intake-r603/active-breadth-reservations.json'))
    mine=[a for a in act3 if a['lane']==rs['lane']]
    if len(mine)!=1 or set(mine[0]['ids'])!=S: errs.append('r603 reservation')
    others=set().union(*[set(a['ids']) for a in act3 if a['lane']!=rs['lane']])
    cov={int(k) for k in J(os.path.join(LN,'root-mathdb-breadth-intake-r603/coverage-delta.json'))}
    prot=set(rs['protected_ids'])|{int(k) for k in J(os.path.join(LN,'root-mathdb-breadth-intake-r603/adjudications.json'))}
    if len(cov)!=6033 or S&cov or S&others or S&prot: errs.append('disjointness')
    # 4. literal records re-read in place
    D=J(os.path.join(ME,'dispositions.json'))
    if len(D)!=50 or [d['mathdb_id'] for d in D]!=ids: errs.append('dispositions not exactly the 50 assigned ids')
    lines={}
    for d in D: lines.setdefault(d['corpus_chunk'],{})[d['line']]=d
    for ch,want in lines.items():
        with open(os.path.join(B,ch),'rb') as f:
            for ln,raw in enumerate(f,1):
                if ln in want:
                    d=want[ln]; raw=raw.rstrip(b'\n'); r=json.loads(raw.decode('utf-8'))
                    can=json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')
                    if (r['mathdb_id']!=d['mathdb_id'] or hashlib.sha256(raw).hexdigest()!=d['line_sha256'] or hashlib.sha256(can).hexdigest()!=d['canonical_record_sha256']
                        or (r.get('statement') or '')!=d['statement'] or hashlib.sha256(d['statement'].encode('utf-8')).hexdigest()!=d['statement_utf8_sha256']):
                        errs.append('record mismatch %s'%d['mathdb_id'])
                    want[ln]=None
        if any(v is not None for v in want.values()): errs.append('lines not found in '+ch)
    for d in D:
        if d['credit']!=0 or d['body_confirmed'] or d['counted_as_complete_statement']!=(d['statement_assessment']=='self_contained'): errs.append('disposition fields %s'%d['mathdb_id'])
    P=J(os.path.join(ME,'proposals.json'))
    if len(P)>3 or any(p['credit']!=0 for p in P): errs.append('proposals')
    # 5. P1 certificate: exact lazy-1/2 Ollivier curvature >=0 on all pairs; sphere 2 has 9>8 vertices
    def mul(u,v): return tuple(u[i] for i in v)
    def inv(u):
        r=[0]*len(u)
        for i,x in enumerate(u): r[x]=i
        return tuple(r)
    a=(3,2,0,1,4); Sg=[a,inv(a),(3,1,4,0,2),(2,4,0,3,1)]
    V=[tuple(range(5))]; ix={V[0]:0}; k=0
    while k<len(V):
        for s in Sg:
            g=mul(V[k],s)
            if g not in ix: ix[g]=len(V); V.append(g)
        k+=1
    n=len(V); adj=[sorted({ix[mul(V[i],s)] for s in Sg}) for i in range(n)]
    def bfs(x):
        Dd=[-1]*n; Dd[x]=0; fr=[x]
        while fr:
            nf=[]
            for u in fr:
                for w in adj[u]:
                    if Dd[w]<0: Dd[w]=Dd[u]+1; nf.append(w)
            fr=nf
        return Dd
    dist=[bfs(i) for i in range(n)]
    def kap(x,y):
        U=[x]*4+adj[x]; W=[y]*4+adj[y]
        return 1-F(min(sum(dist[u][w] for u,w in zip(U,p)) for p in set(itertools.permutations(W))),8*dist[x][y])
    mk=min(kap(x,y) for x in range(n) for y in range(x+1,n))
    sph=[sum(1 for t in dist[0] if t==r) for r in range(max(dist[0])+1)]
    if n!=20 or any(len(x)!=4 for x in adj) or mk<0 or sph!=[1,4,9,6]: errs.append('P1 certificate')
    rep['P1']={'n':n,'min_kappa_all_pairs':str(mk),'spheres':sph}
    # 6. P2 instance K3, b=3
    N=[0b110,0b101,0b011]
    def dyn(t):
        for D0 in sorted(range(8),key=lambda s:bin(s).count('1')):
            H=D0; ch=True
            while ch:
                ch=False
                for u in range(3):
                    if not H>>u&1 and bin(H&N[u]).count('1')>=t[u]: H|=1<<u; ch=True
            if H==7: return bin(D0).count('1')
    vacc=max(dyn(t) for t in itertools.product(range(3),repeat=3) if sum(t)==3)
    if not (vacc==1 and dyn((0,0,0))==0 and min(2+2+0,4)>3): errs.append('P2 instance')
    rep['P2']={'vacc':vacc,'dyn_empty_matching':dyn((0,0,0))}

try:
    _checks()
except Exception as ex:
    errs.append('exception: %s: %s'%(type(ex).__name__,ex))
rep['errors']=errs; rep['result']='PASS' if not errs else 'FAIL'
print(json.dumps(rep,sort_keys=True)); sys.exit(1 if errs else 0)
