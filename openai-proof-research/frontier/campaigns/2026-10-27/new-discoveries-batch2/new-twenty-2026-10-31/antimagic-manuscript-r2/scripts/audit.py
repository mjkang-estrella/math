"""Fresh transcription of AntimagicLabel.lean; no Lean execution."""
from pathlib import Path
import json, hashlib, zipfile, runpy
O=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
with zipfile.ZipFile(O/'lean-source.zip') as z:
    lean=z.read('AntimagicLabel.lean')
assert lean==(O/'packet-extracted/AntimagicLabel.lean').read_bytes()
# Natural subtraction, division and all branch orders follow the frozen text.
def sub(a,b):
    assert a>=b, (a,b)
    return a-b
def internal(t,n,h,i):
    N=sum(t**g for g in range(1,n)); Z=sub(N,t)//2+1
    if h==1: return Z if i==0 else sub(N,t)+1+i
    P=sub(4,i) if t==2 and h==2 and i in (1,3) else i
    r=sum(t**g for g in range(h+1,n))+P; d=1+r//2
    return sub(Z,d) if r%2==0 else Z+d
def sigma(k,a): return 2*a if a<=k else sub(2*sub(a,k),1)
def frozen(t,n,h,i):
    if n==1: return i+1
    if n==2:
        if t==2: return (1 if i==0 else 4) if h==1 else (2 if i==0 else 3 if i==1 else 6 if i==2 else 5)
        s=t//2
        if h==1: return 2 if i==0 else sub(3*s+2,i)
        p,j=divmod(i,t)
        if p==0: return 1 if j==0 else j+2 if j<=s else 2*s+1+j
        a=sub(p,1); k=sub(s,1); q=sub(t,1); beta=2*t+sub(s,1)*q
        if j<sub(t,2):
            b=j//2
            return 2*t+b*q+a+1 if j%2==0 else 2*t+sub(sub(t,1),b)*q+sub(q,a)
        if a<=k: return beta+2*a+1 if j==sub(t,2) else sub(beta+3*k+2,a)
        r=sub(a,k)
        return beta+2*r if j==sub(t,2) else sub(beta+4*k+3,r)
    if h<n: return internal(t,n,h,i)
    N=sum(t**g for g in range(1,n)); q=t**sub(n,1); Z=sub(N,t)//2+1
    pl=internal(t,n,sub(n,1),i//t); a=sub(pl,Z) if Z<pl else sub(q+1+pl,Z); j=i%t
    lam=lambda b,x:N+sub(b,1)*q+x
    if j<sub(t,2):
        b=j//2+1
        return lam(b,a) if j%2==0 else lam(sub(t+1,b),sub(q+1,a))
    if j==sub(t,2): return lam(t//2,a)
    return lam(t//2+1,sub(q+1,sigma(q//2,a)))
# Independent graph incidence aggregation, rather than deriving weights from identities.
def weights(t,n,rows):
    w={(h,i):0 for h in range(n+1) for i in range(t**h)}
    for h,row in enumerate(rows,1):
        for i,x in enumerate(row): w[h,i]+=x; w[h-1,i//t]+=x
    return [[w[h,i] for i in range(t**h)] for h in range(n+1)]
checks={}; cases=[]
def ck(name,condition,t,n):
    assert condition, (name,t,n)
    checks.setdefault(name,[]).append([t,n])
legacy=runpy.run_path(str(O/'scripts/verify.py'))['label']
for t in (2,4,6,8):
 for n in range(1,6):
    rows=[[frozen(t,n,h,i) for i in range(t**h)] for h in range(1,n+1)]
    w=weights(t,n,rows); flat=[x for row in rows for x in row]; m=sum(t**h for h in range(1,n+1)); leaves=set(rows[-1]); colors=set(x for row in w for x in row)
    def check(name,ok): ck(name,ok,t,n)
    check('S1: row sizes t^h; edge count sum t^h; t^n distinct leaf weights',len(flat)==m and len(leaves)==t**n and w[-1]==rows[-1])
    check('S1: full bijection [1,m]; independent incidence weights; every edge proper; exact t^n+1 colours',sorted(flat)==list(range(1,m+1)) and all(w[h][i]!=w[h-1][i//t] for h in range(1,n+1) for i in range(t**h)) and len(colors)==t**n+1)
    check('Frozen text transcription agrees with independent inherited verifier on every edge',all(x==legacy(t,n,h,i) for h,row in enumerate(rows,1) for i,x in enumerate(row)))
    # Degree, diameter and maximum-label endpoint used in the lower bound.
    check('S1/S2/S8: degrees t, t+1,1; diameter 2n; maximal-edge parent weight > m',t>=2 and 2*n>=2 and all(w[h-1][i//t]>m for h,row in enumerate(rows,1) for i,x in enumerate(row) if x==m))
    c={'t':t,'n':n,'edges':m,'colors':len(colors),'root_weight':w[0][0]}
    if n==1:
        check('S2 depth one: labels 1..t; root t(t+1)/2 > t; t+1 colours',rows[0]==list(range(1,t+1)) and w[0]==[t*(t+1)//2] and w[0][0]>t)
    elif n==2 and t==2:
        check('S2 Figure 5: rows (1,4),(2,3,6,5); weights 5,6,15; set {2,3,5,6,15}',rows==[[1,4],[2,3,6,5]] and w[:2]==[[5],[6,15]] and colors=={2,3,5,6,15})
    elif n==2:
        s=t//2; q=t-1; k=s-1; M=t*t+t; beta=2*t+k*q; H=4*t+t*q+1; D=(s-1)*H+2*beta+3*k+3; C=D+3*s+1
        S=set(rows[1][:t]); B=set(range(2*t+1,M+1))
        check('S3 definitions s,q,k,M,beta; root labels and set; exceptional slots and S*',M==m and rows[0]==[2]+[3*s+2-p for p in range(1,q+1)] and set(rows[0])=={2}|set(range(s+3,3*s+2)) and rows[1][:t]==[1]+[j+2 if j<=s else 2*s+1+j for j in range(1,t)] and S=={1}|set(range(3,s+3))|set(range(3*s+2,4*s+1)))
        check('S3: root and S* partition [1,2t]; B=[2t+1,M] has tq entries',not (S&set(rows[0])) and S|set(rows[0])==set(range(1,2*t+1)) and set(rows[1][t:])==B and len(B)==t*q)
        first=[];second=[]
        for p in range(1,q+1):
            a=p-1; row=rows[1][p*t:(p+1)*t]
            check('S3: every outer pair formula and H',all(row[2*b:2*b+2]==[2*t+b*q+a+1,2*t+(t-1-b)*q+q-a] and sum(row[2*b:2*b+2])==H for b in range(s-1)))
            pair=[beta+2*a+1,beta+3*k+2-a] if a<=k else [beta+2*(a-k),beta+4*k+3-(a-k)]
            first.append(pair[0]-beta);second.append(pair[1]-beta)
            check('S3: both middle branches; sum 2beta+3k+3+a; tuple D+p-1; parent C',row[-2:]==pair and sum(pair)==2*beta+3*k+3+a and sum(row)==D+p-1 and w[1][p]==C)
        check('S3: four middle coordinate sets cover beta+[1,4k+2]',set(first)==set(range(1,2*k+2,2))|set(range(2,2*k+1,2)) and set(second)==set(range(2*k+2,3*k+3))|set(range(3*k+3,4*k+3)) and sorted(first+second)==list(range(1,4*k+3)))
        check('S3: root M; sum S*=2s(4s+1)-M=t^2; exceptional weight t^2+2',w[0]==[2+(2*s-1)*(2*s+2)]==[M] and sum(S)==2*s*(4*s+1)-M==t*t and w[1][0]==t*t+2)
        check('S3: M and t^2+2 in B; C>t(2t+1)>M; exception>2t and !=M; exact leaf set plus C',M in B and t*t+2 in B and C>t*(2*t+1)>M and t*t+2>2*t and t*t+2!=M and colors==leaves|{C})
        c.update(H=H,D=D,C=C,beta=beta)
    else:
        N=sum(t**h for h in range(1,n));q=t**(n-1);k=q//2;R=(N-t)//2;Z=R+1;L=2*N+t*q+1;C=t//2*L+Z; W=Z+(t-1)*N-(t-1)*(t-2)//2
        check('S4 definitions N,q,k,R,Z,m; internal labels [1,N]; leaves [N+1,m]',m==N+t*q and 2*k==q and 2*R==N-t and sorted(flat[:-t**n])==list(range(1,N+1)) and leaves==set(range(N+1,m+1)))
        cursor=0
        for h in range(n-1,1,-1):
            off=sum(t**g for g in range(h+1,n)); P=[4-i if t==2 and h==2 and i in (1,3) else i for i in range(t**h)]
            check('S4: O_h even concatenated intervals; P_h row permutation; every internal shell label',off==cursor and off%2==0 and sorted(P)==list(range(t**h)) and rows[h-1]==[Z-(1+(off+i)//2) if (off+i)%2==0 else Z+1+(off+i)//2 for i in P])
            cursor+=t**h
        check('S4: shell pairs 1..R cover central-hole interval; row one completes [1,N]',cursor==2*R and set(flat[t:-t**n])==set(range(1,N-t+2))-{Z} and rows[0]==[Z]+list(range(N-t+2,N+1)))
        sig=[sigma(k,a) for a in range(1,q+1)];delta=[a-v for a,v in enumerate(sig,1)]
        check('S4/S5: sigma lower evens upper odds; delta=-a or k+1-j; both permutations',sig==list(range(2,q+1,2))+list(range(1,q,2)) and sorted(delta)==list(range(-k,0))+list(range(1,k+1)) and delta==[-a for a in range(1,k+1)]+[k+1-j for j in range(1,k+1)])
        aa=[];expected=[]
        for p in rows[-2]:
            a=p-Z if p>Z else q+1+p-Z;aa.append(a);lam=lambda b,x:N+(b-1)*q+x
            row=[]
            for b in range(1,t//2):row.extend([lam(b,a),lam(t+1-b,q+1-a)])
            row.extend([lam(t//2,a),lam(t//2+1,q+1-sigma(k,a))]);expected.extend(row)
            check('S4/S5: a parameter, lambda slot families; nonnegative arguments; cancellation p+delta=Z; outer L and middle L+delta',1<=a<=q and 1<=sigma(k,a)<=q and p+a-sigma(k,a)==Z and all(sum(row[2*b:2*b+2])==L for b in range(t//2-1)) and sum(row[-2:])==L+a-sigma(k,a))
        check('S4: final parents Z+-[1,k]; a permutes [1,q]; all leaf slot families and block bijections',set(rows[-2])=={Z+d for d in range(-k,k+1) if d} and sorted(aa)==list(range(1,q+1)) and expected==rows[-1] and all(len([x for x in expected if N+(b-1)*q<x<=N+b*q])==q for b in range(1,t+1)))
        check('S5: L=2N+tq+1>m; C=(t/2)L+Z>m; constant final parents; exact Lambda union C',L>m and C>m and set(w[-2])=={C} and colors==leaves|{C})
        if t>=4:
            check('S5: every middle child sum tZ; weights incoming+tZ; W formula',all(sum(rows[h][t*i:t*i+t])==t*Z and w[h][i]==rows[h-1][i]+t*Z for h in range(1,n-1) for i in range(t**h)) and w[0]==[W])
            check('S5: geometric identities; N-t<2q and <=2q-2; Z<=q; tZ-N=(t/2-1)(N-t)>=0',(t-1)*N==t**n-t and N==2*Z+t-2 and N-t<2*q and N-t<=2*q-2 and Z<=q and t*Z-N==(t//2-1)*(N-t)>=0)
            check('S5: N+1<=tZ+f<=tZ+N<=m; W-tZ=(t-1)N/2>N; W<tN=m-t<m',all(N+1<=x<=t*Z+N<=m for row in w[1:-2] for x in row) and 2*(W-t*Z)==(t-1)*N and W-t*Z>N and W<t*N==m-t<m)
        else:
            check('S6: N=2^n-2=2Z; q=Z+1; m=4Z+2; Z>=3; root edges Z,2Z',N==2**n-2==2*Z and q==Z+1 and m==4*Z+2 and Z>=3 and rows[0]==[Z,2*Z])
            check('S6: patched row two (2,2Z-1,1,2Z-2); child sums 2Z+1,2Z-1; weights 3Z,3Z+1,4Z-1 in Lambda',rows[1]==[2,2*Z-1,1,2*Z-2] and [sum(rows[1][:2]),sum(rows[1][2:])]==[2*Z+1,2*Z-1] and w[:2]==[[3*Z],[3*Z+1,4*Z-1]] and all(x in leaves for row in w[:2] for x in row))
            check('S6: other middle child sums 2Z and translated weights in Lambda',all(sum(rows[h][2*i:2*i+2])==2*Z and w[h][i]==rows[h-1][i]+2*Z and w[h][i] in leaves for h in range(2,n-1) for i in range(2**h)))
            if n>=4:check('S6: n>=4 Z>=7; row-two weights and first-row adjacency inequalities',Z==2**(n-1)-1>=7 and w[2]==[2*Z+2,4*Z-1,2*Z+1,4*Z-2] and 3*Z+1 not in w[2][:2] and 4*Z-1 not in w[2][2:])
        c.update(N=N,q=q,k=k,R=R,Z=Z,L=L,C=C,W=W)
    if n==3 and t in (2,4):c.update(edge_rows=rows,weight_rows=w)
    cases.append(c)
# Exact printed examples are generated from the fresh formula, then compared.
a=next(c for c in cases if c['t']==2 and c['n']==3); b=next(c for c in cases if c['t']==4 and c['n']==3)
assert a['edge_rows']==[[3,6],[2,5,1,4],[10,12,8,11,9,14,7,13]] and a['weight_rows'][:-1]==[[9],[10,11],[24]*4]
assert (b['N'],b['Z'],b['q'],b['edges'],b['root_weight'],b['C'],b['colors'])==(20,9,16,84,66,219,65)
assert b['edge_rows'][:2]==[[9,18,19,20],[8,10,7,11,6,12,5,13,4,14,3,15,2,16,1,17]] and b['weight_rows'][1]==[45,54,55,56] and b['edge_rows'][2][:4]==[36,69,52,54] and sum(b['edge_rows'][2][:4])==211
# Negative control reconstructs the bad printed tuple, rather than silently replacing it.
wrong=weights(2,3,[[3,6],[2,5,1,4],[10,14,8,13,9,12,7,11]])
assert wrong[2]==[26,26,22,22]
for name in ('paper.md','PROOF.md'):
 p=O/name;s=p.read_text();s=s.replace('H = 4t+(t−1)q+1','H = 4t+tq+1').replace('(10,14,8,13,9,12,7,11)','(10,12,8,11,9,14,7,13)').replace('(26,26,26,26)','(24,24,24,24)').replace('[7,14] ∪ {26}','[7,14] ∪ {24}')
 p.write_text(s)
p=O/'paper.md';s=p.read_text();note="Round 2 corrects the t = 2, n = 3 worked example (and any other items listed in the dossier’s AUDIT.md); the Lean packet is unchanged."
if note not in s:s=s.replace('## 7. Formal correspondence, audits and reproducibility','## 7. Formal correspondence, audits and reproducibility\n\n'+note)
p.write_text(s)
report={'status':'PASS','diagnostic_only':True,'lean_executed':False,'formula_source_sha256':hashlib.sha256(lean).hexdigest(),'cases':cases,'checks':[{'statement':k,'evaluations':len(v),'parameter_cases':sorted(set(map(tuple,v)))} for k,v in checks.items()],'negative_control_wrong_parent_weights':wrong[2],'corrections':['Section 3 outer-pair H corrected to 4t+tq+1 in paper.md and PROOF.md','binary n=3 leaf row, final-parent weights 24, colour set [7,14] union {24}'],'further_errors_found':1}
(O/'receipts/numerical-audit.json').write_text(json.dumps(report,indent=2)+'\n')
lines=['# Round 2 numerical audit','', 'DRAFT; diagnostic finite checks, not a proof or acceptance. Zero accepted credit; root alone accepts.','', 'Fresh Python transcription from the hash-bound AntimagicLabel.lean text in the frozen source ZIP, including checked natural subtractions. Every edge was also compared with the independently inherited verifier. Vertex weights were recomputed by adding each edge to both graph endpoints, independently of the identities under test. No Lean, lake or leanchecker was run.','', '## Coverage and results','', 'All 20 pairs t in {2,4,6,8}, n in {1,2,3,4,5} passed full bijectivity, properness and exact colour-count checks. Each specialized statement below was checked for every applicable pair; repeated evaluations include every parent or pair of slots. Out-of-domain cases are excluded, not counted as passes. Exact data and case lists are in receipts/numerical-audit.json.','']
for k,v in checks.items():lines.append('- PASS: '+k+'. Cases: '+', '.join(f'({t},{n})' for t,n in sorted(set(map(tuple,v))))+f'; {len(v)} evaluations.')
lines+=['','## Corrections and exact examples','','The reported binary depth-three error is corrected in paper.md and PROOF.md (Section 6). The old leaf row (10,14,8,13,9,12,7,11) gives final-parent weights (26,26,22,22), confirmed as a negative control; it cannot support the old claimed constant 26. The frozen formula gives rows (3,6), (2,5,1,4), (10,12,8,11,9,14,7,13), weights (9), (10,11), (24,24,24,24), then the leaf labels; N=6, Z=3, q=4, m=14, C=24, spectrum [7,14] union {24}, nine colours. All printed example numbers were checked.','','The t=4,n=3 example is unchanged: N=20,Z=9,q=16,m=84; internal rows (9,18,19,20), (8,10,7,11,6,12,5,13,4,14,3,15,2,16,1,17); W=66, row-one weights (45,54,55,56), 16 parents of weight 219; leaves [21,84], 65 colours. First parent p=8 has a=16, sigma=15, tuple (36,69,52,54), sum 211 and total 219. All these values passed.','','## Noncomputational numbers and formula limits','','Theorem/lemma/figure numbers, bibliographic years/pages/DOIs, version identifiers, hashes, dates, reported review counts and arXiv identifiers are provenance data, not evaluations of the labelling formula. They remain attributed to the frozen sources and inherited receipts; the numerical audit does not claim to re-prove published lemmas or rerun inherited formal builds or literature searches. The cited odd-q tuple construction is exercised by every depth-two t>=4 case; the even-q average obstruction follows from the integer versus half-integer means. Abstract theorem scope, endpoint signatures and graph transport are inherited formal correspondence claims, not new formal verification. The finite checks do not replace those proofs.','','Every line of paper.md containing digits is indexed in receipts/paper-numeric-lines.json to make the mathematical and provenance coverage reviewable. One further formula correction was required: Section 3 outer pairs sum to H=4t+tq+1, not 4t+(t-1)q+1. For t=4 the outer pair (9,20) sums to 29, whereas the old expression gives 26. The definitions of D and C were already structurally correct but inherit H, so correcting H restores their asserted tuple and parent identities. This is corrected in both manuscript sources. All depth-two checks above use the corrected H. The visible errata note is added in Section 7.']
(O/'AUDIT.md').write_text('\n'.join(lines)+'\n')
(O/'receipts/paper-numeric-lines.json').write_text(json.dumps([{'line':i,'text':line,'category':'provenance / formal correspondence' if i> s.splitlines().index('## 7. Formal correspondence, audits and reproducibility') else 'mathematics / source attribution'} for i,line in enumerate(s.splitlines(),1) if any(c.isdigit() for c in line)],indent=2)+'\n')
print('PASS',len(cases),'cases;',len(checks),'statement groups;',sum(map(len,checks.values())),'evaluations')
