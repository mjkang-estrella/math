#!/usr/bin/env python3
"""Read-only Structural194 discovery intake; artifact checks and finite rechecks only, no mathematical gate."""
import collections,datetime,hashlib,importlib.util,itertools,json,random,re,shutil,stat,subprocess,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r194';V=A/'private'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
FOLDERS=['preprints/Filtered-chromatic-splitting-at-generic-primes-September-25-2026/','preprints/The-height-three-chromatic-overlap-an-explicit-filtration-and-its-attachments-September-27-2026/','preprints/A-rational-obstruction-to-strong-chromatic-splitting-at-height-three-September-25-2026/','preprints/Failure-of-finite-assembly-for-a-chromatic-overlap-at-the-prime-three-September-25-2026/','preprints/Counterexamples-to-weak-chromatic-splitting-sphere-kernels-and-descent-exponents-September-27-2026/']
WRAPPERS=[('build/paper.tex',918,'66a0d3da071a9cb576c52fa055fa588ab25f5db0'),('build/paper.tex',1196,'5dd072e006a3d90800a23ffed661ec6aa1b9fcfa'),('build/main.tex',1057,'65324c62fb728f11dd65b8fdd74b0627a52d8d3c'),('build/paper.tex',3051,'795f08a402bc0d06f4ed1ef24a78b1afa09c3153'),('build/main.tex',1122,'3ac56b00cf250ad0c47482d2e98426feabdc554b')]
FINAL='30eeeb5985e8b56204c643f122a23a098639971b78e20783911eaedee6e0d640';MANIFEST='0f8f84c6ae4bad15eae6a6ca391d29800c295b57972067e994e9b26ae86a7129';REPORT='54eb61cb1f5e7c2835b81f6cd6d5cc4ad0c6575cc99c9da0a46590c7f6426520'
def read(p):return json.loads(p.read_bytes())
def lines(p):return [json.loads(l)for l in p.read_text().splitlines()if l.strip()]
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def span(p,s,e):
    assert not p.is_symlink()and p.stat().st_nlink==1
    with p.open('rb')as f:f.seek(s);d=f.read(e-s)
    assert len(d)==e-s;return d
ENV={'PYTHON_COLORS':'0','PATH':'/usr/bin:/bin'}
def verifier(root,F,M,R):
    return subprocess.run(['python','-I','-B',str(A/'verify_packet.py'),'--root',str(root),'--final-sha256',F,'--manifest-sha256',M,'--report-sha256',R],cwd=P,capture_output=True,text=True,env=ENV)
def clean(s):return re.sub(r'\x1b\[[0-9;]*m','',s)

# ---------------- parent finite rechecks of the retained bookkeeping (independent of the child's text) ----------------
# Graded "homotopy" bookkeeping: a spectrum is a dict degree -> multiset of symbols; Q[-k] contributes 'Qp' in degree -k.
def shift(X,j):return {d+j:list(v)for d,v in X.items()}
def wedge(*Xs):
    out=collections.defaultdict(list)
    for X in Xs:
        for d,v in X.items():out[d]+=v
    return {d:sorted(v)for d,v in out.items()if v}
def Q(k):return {-k:['Qp']}
def parent_rechecks():
    R={}
    # (2.2) low stems of A_1=L_1 S at p>=5 and (2.1) splitting F_S(A_1,A_2) = A_1[-2] v Q[-4] v Q[-5]; only degrees -1..-3 of A_1 are used.
    A1={-1:[],-2:['Qp/Zp'],-3:[]}
    F=wedge(shift(A1,-2),Q(4),Q(5))   # degrees -3..-5 of F_S(A_1,A_2)
    # [A_1[-i], Sigma^e A_2] = pi_{-i-e} F ; rows (Sigma A_2, A_2), columns (A_1[-3], A_1[-4])
    M=[[F.get(-3-1,[]),F.get(-4-1,[])],[F.get(-3,[]),F.get(-4,[])]]
    R['middle_matrix_2_3']=M;assert M==[[['Qp','Qp/Zp'],['Qp']],[[],['Qp','Qp/Zp']]]
    # (2.5) Gamma P from the triangle A_2 -> P -> A_1[-3] -a-> Sigma A_2 with Gamma a = 0 by degrees
    GA1=Q(2);GA2=wedge(Q(4),Q(4),Q(5));GU3=shift(GA1,-3);SGA2=shift(GA2,1)
    assert not set(GU3)&set(SGA2)   # Gamma a: Q[-5] -> Q[-3]^2 v Q[-4] vanishes by degrees
    GP=wedge(GA2,GU3);R['GammaP_2_5']=GP;assert GP=={-4:['Qp','Qp'],-5:['Qp','Qp']}
    # consistency with i105's Gamma F_4 = Q[-4]^2 v Q[-5]^4 v Q[-6]^2 computed two ways: W v U with Gamma d = 0, and C (x) P = P v P[-1]
    GW=wedge(GA2,shift(GA2,-1));GU=wedge(GU3,shift(GU3,-1));GF4=wedge(GW,GU);GCP=wedge(GP,shift(GP,-1))
    assert GF4==GCP=={-4:['Qp']*2,-5:['Qp']*4,-6:['Qp']*2};R['GammaF4_two_ways']=GF4
    # Section 8: Adams-filtration inequalities 2(p-1)^2 >= a^2+2 for a=p and a=p+1 over odd primes
    ok_p={p:2*(p-1)**2-(p*p+2)for p in[3,5,7,11,13,17,19,23,29,31]};ok_p1={p:2*(p-1)**2-((p+1)**2+2)for p in ok_p}
    assert all(v>=0 for p,v in ok_p.items()if p>=5)and ok_p[3]<0 and all(v>=0 for p,v in ok_p1.items()if p>=7)and ok_p1[5]<0 and ok_p1[3]<0
    assert all(ok_p[p]==p*(p-4)and ok_p1[p]==p*p-6*p-1 for p in ok_p);R['section8_inequalities']={'a=p':ok_p,'a=p+1':ok_p1}
    # Section 6: rows s=0,1 carry omega^j in t=2j; rows s=3,4 carry delta omega^j in t=2j; total degree n=t-s. Recompute (6.1), the cofiber lines (6.2),
    # the zeta (degree -1) bookkeeping on omega powers and the exterior-pair degrees.
    def V(n):
        out=[]
        for s in(0,1,3,4):
            t=n+s
            if t%2==0:out.append(('delta' if s>=3 else '')+'omega^%d'%(t//2))
        return out
    for r in range(-4,5):
        assert V(2*r)==['omega^%d'%r,'deltaomega^%d'%(r+2)]and V(2*r-1)==['omega^%d'%r,'deltaomega^%d'%(r+1)]
    # cofiber of the unit/zeta lower-row sections: upper lines only; zeta maps degree 2r-1 upper line to degree 2r-2 upper line
    upper=lambda n:[x for x in V(n)if x.startswith('delta')]
    assert all(upper(2*r-1)==upper(2*r-2)==['deltaomega^%d'%(r+1)]for r in range(-4,5))
    assert upper(-3)==upper(-4)==['deltaomega^0']and [x for x in V(0)if not x.startswith('delta')]==[x for x in V(-1)if not x.startswith('delta')]==['omega^0']
    R['section6_pairs']={'unit_pair_degrees':[0,-1],'delta_pair_degrees':[-3,-4],'delta_pair_line':'F_x(delta) (omega^0)'}
    # Sections 4-5: Gamma_Z N = fib(psi-1) vanishes iff psi-1 is invertible; a contraction of the two-term complex via (psi-1)^{-1} exists while N != 0.
    rng=random.Random(194);cnt={'invertible':0,'noninvertible':0}
    for p in(5,7):
        for _ in range(60):
            n=rng.randint(1,5);Mx=[[rng.randrange(p)for _ in range(n)]for _ in range(n)]
            D=[[(Mx[i][j]-(1 if i==j else 0))%p for j in range(n)]for i in range(n)]
            rk=rank_mod(D,p);ker=n-rk;coker=n-rk
            if ker==0:cnt['invertible']+=1;assert coker==0 and n>0
            else:cnt['noninvertible']+=1;assert ker==coker>0
    R['psi_minus_one_fixed_points']=cnt;assert cnt['invertible']>0 and cnt['noninvertible']>0
    return R
def rank_mod(M,p):
    M=[r[:]for r in M];rk=0;rows=len(M);cols=len(M[0])if M else 0
    for c in range(cols):
        piv=next((r for r in range(rk,rows)if M[r][c]%p),None)
        if piv is None:continue
        M[rk],M[piv]=M[piv],M[rk];inv=pow(M[rk][c],-1,p);M[rk]=[(x*inv)%p for x in M[rk]]
        for r in range(rows):
            if r!=rk and M[r][c]:f=M[r][c];M[r]=[(a-f*b)%p for a,b in zip(M[r],M[rk])]
        rk+=1
    return rk

def main():
    anchors=read(A/'ANCHORS.json');assert anchors['format']=='r194-detached-anchors-v1'and anchors['sha256']=={'FINAL.md':FINAL,'MANIFEST.json':MANIFEST,'REPORT.md':REPORT}and anchors['verification']=={'artifact_integrity':'verified','mathematical_gate':False,'selected_files':147}and anchors['selected_bytes']==22186011
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors['sha256'].items())
    run=verifier(A,FINAL,MANIFEST,REPORT);assert run.returncode==0 and not run.stderr and json.loads(clean(run.stdout))=={'artifact_integrity':'verified','mathematical_gate':False,'selected_files':147},run
    m=read(A/'MANIFEST.json');assert m['format']=='r194-selected-packet-v1'and m['outside_manifest']==['MANIFEST.json','REPORT.md','ANCHORS.json','private/controls/']and len(m['files'])==147 and sum(x['bytes']for x in m['files'])==22186011;names={x['path']for x in m['files']}
    for x in m['files']:p=A/x['path'];assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']
    rootfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};ctrl={f for f in rootfiles if f.startswith('private/controls/')};assert len(ctrl)==8 and rootfiles==names|{'MANIFEST.json','REPORT.md','ANCHORS.json'}|ctrl and len(rootfiles)==158
    assert {'FINAL.md','DERIVATIONS.md','INTERFACES.md','COMPARISON.md','verify_packet.py','private/READING-LIMITS.md','private/READING-PROGRESS.md','private/brief.txt','private/policy.json','private/authentication.json','private/source-reading-final.json','private/include-edges.json','private/history-extents.json','private/completed-reads.json','private/control-results.json'}<=names
    assert not any(p.is_symlink()for p in A.rglob('*'))
    # pinned tree, canonical blobs exhausting the five folders, wrappers and include edges
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    assert (V/'tree.json').read_bytes()==(P/'sources/preprints-tree.json').read_bytes()
    auth=read(V/'authentication.json');assert len(auth)==85 and not any('error'in x for x in auth)
    for x in auth:
        e=lookup[x['path']];p=V/'source'/x['path'];d=p.read_bytes();assert any(x['path'].startswith(f)for f in FOLDERS)and e['type']=='blob'and len(d)==x['bytes']==e['size']and x['git_blob']==e['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()and sha(p)==x['sha256']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    authpaths=sorted(x['path']for x in auth);blobs_per=[];entries_per=[]
    for f in FOLDERS:
        blobs_per.append(sum(1 for k,e in lookup.items()if k.startswith(f)and e['type']=='blob'));entries_per.append(sum(1 for k in lookup if k.startswith(f)))
    assert sorted(k for k,e in lookup.items()if e['type']=='blob'and any(k.startswith(f)for f in FOLDERS))==authpaths and blobs_per==[17,18,18,15,17]and sum(entries_per)==95
    sel=read(V/'selected.json');assert sorted(x['path']for x in sel)==authpaths and all(lookup[x['path']]['sha']==x['sha']and lookup[x['path']]['size']==x['size']for x in sel)
    for f,(w,nb,gb)in zip(FOLDERS,WRAPPERS):assert lookup[f+w]['size']==nb and lookup[f+w]['sha']==gb
    ie=read(V/'include-edges.json');assert len(ie)==74
    by=collections.defaultdict(list)
    for e in ie:by[e['source']].append(e)
    wrapper_orders={}
    for src,edges in by.items():
        wb=(V/'source'/src).read_bytes();ins=re.findall(rb'\\(input|bibliography)\{([^}]*)\}',wb);assert len(ins)==len(edges),src
        for (k,t),e in zip(ins,edges):
            s0,s1=e['bytes'];cmd=wb[s0:s1];assert cmd.startswith(b'\\'+k)and t in cmd and e['kind']==k.decode()and e['target']==t.decode()
            if not e['target'].startswith('glyphtounicode'):
                tgt=Path(src).parent/(e['target']+('.bib'if e['kind']=='bibliography'else'.tex'));assert tgt.as_posix()in lookup and(V/'source'/tgt).is_file(),tgt
        if src.endswith(('build/paper.tex','build/main.tex')):wrapper_orders[src.split('/')[1]]=[e['target']for e in edges]
    assert set(by)=={f+w for f,(w,_,_)in zip(FOLDERS,WRAPPERS)}|{FOLDERS[2]+'build/preamble.tex',FOLDERS[4]+'build/preamble.tex'}
    # every .tex blob of each folder is reached from its wrapper (directly or through a nested preamble input)
    reached=set()
    for src,edges in by.items():
        for e in edges:
            if not e['target'].startswith('glyphtounicode'):reached.add((Path(src).parent/(e['target']+('.bib'if e['kind']=='bibliography'else'.tex'))).as_posix())
    texblobs={k for k in authpaths if k.endswith(('.tex','.bib'))and not k.endswith(('build/paper.tex','build/main.tex'))};assert texblobs==reached,texblobs^reached
    assert [t for t in wrapper_orders[FOLDERS[0].split('/')[1]]if t.startswith('sections')]==['sections/01-introduction','sections/02-assembly','sections/03-rings','sections/04-coefficient-scope','sections/05-support','sections/08-compact','sections/09-boundary','sections/10-full-frame','sections/06-constants','sections/07-generators','sections/10-constant-module','sections/11-spectral']
    appendix={}
    for f,(w,_,_)in zip(FOLDERS,WRAPPERS):
        wb=(V/'source'/f/w).read_bytes();appendix[f.split('/')[1][:24]]=[t.decode()for _,t in re.findall(rb'\\(input)\{([^}]*)\}',wb[wb.index(b'\\appendix'):])]if b'\\appendix'in wb else []
    # complete source reading record: 80 text blobs with full extents, 5 PDFs authenticated only
    srf=read(V/'source-reading-final.json');assert len(srf)==85 and sorted(x['path']for x in srf)==authpaths
    for x in srf:
        p=V/'source'/x['path'];assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']
        if x['path'].endswith('.pdf'):assert x['semantic_read']is False and x['extents']==[]
        else:assert x['semantic_read']is True and x['extents']==[[0,x['bytes']]];p.read_bytes().decode('utf-8')
    assert sum(1 for x in srf if x['path'].endswith('.pdf'))==5
    ch=read(V/'chunks.json');assert len(ch)==58 and all((V/'source'/x['path']).is_file()for x in ch)
    for row in lines(V/'display-ledger.jsonl'):assert hashlib.sha256(span(V/'source'/row['path'],row['start'],row['end'])).hexdigest()==row['sha256']
    for row in lines(V/'chunk-display.jsonl'):assert hashlib.sha256(span(V/'source'/row['path'],*row['extent'])).hexdigest()==row['sha256']
    rec=lines(V/'recovery-extents.jsonl');assert len(rec)==6 and rec[5]['event'].startswith('cwd deviation')
    for row in rec[:4]:s,e=row['extent'];assert 0<=s<e<=(V/'source'/row['path']).stat().st_size
    # the r39 recovery row hashes the whole 7763-byte file (its extent ends at EOF); the copied section itself is checked below
    assert rec[4]['extent']==[6297,7763]and sha(P/rec[4]['path'])==rec[4]['sha256']and(P/rec[4]['path']).stat().st_size==7763
    # direct reads, brief copy, catalogue span, completed copies, history spans
    assert (V/'brief.txt').read_bytes()==(B/'expanded-target-2026-10-17/fresh-structural-r194-brief.txt').read_bytes()and sha(V/'brief.txt')=='11c7864441c0c8ef46d1d572bf5214acea8fb3f8a9fd22962c47c01bf5ef319a'and(V/'brief.txt').stat().st_size==30960
    assert (V/'contracts/acceptance-4801-6347.txt').read_bytes()==span(P/'frontier/NEW-TEN-2026-10-14.md',4801,6347)
    assert (V/'contracts/AGENTS.md').read_bytes()==(P/'AGENTS.md').read_bytes()and(V/'contracts/upstream.json').read_bytes()==(P/'sources/upstream.json').read_bytes()
    cat=span(P/'sources/CONTENTS.md',540867,544391);assert (V/'Source318.txt').read_bytes()==cat and hashlib.sha256(cat).hexdigest()=='e84108b781fe07f20fe9d4d6d10cd0cda593ecbb7588ae0df2d0cc83887eaa76'and cat.startswith(b'**318. ')and b'lean/docs/'not in cat
    ce=read(V/'completed-reads.json');assert [x['path'][len('frontier/campaigns/2026-10-14/'):]for x in ce]==['discovery-structural-r193-parent/assessment.md','fresh-structural-discovery-r193/FINAL.md','fresh-structural-discovery-r193/INTERFACES.md','fresh-structural-discovery-r193/DERIVATIONS.md','fresh-structural-discovery-r193/COMPARISON.md','fresh-structural-discovery-r193/private/READING-LIMITS.md']
    for x in ce:o=P/x['path'];assert o.stat().st_size==x['bytes']and sha(o)==x['sha256']
    assert ce[0]['sha256']=='11020f2e66de8143ab588aa32160a271008d2c34aab9676bff842308a0159be0'
    hx=read(V/'history-extents.json');assert len(hx)==17
    for x in hx:assert hashlib.sha256(span(P/x['path'],x['start'],x['end'])).hexdigest()==x['sha256']
    for name,size,copy in(('frontier/iterations/i105-chromatic-homotopy-discovery.md',31282,'i105-chromatic-homotopy-discovery.md'),('frontier/iterations/i107-rational-tail-attachment.md',39535,'i107-rational-tail-attachment.md')):
        ex=sorted((x['start'],x['end'])for x in hx if x['path']==name);assert ex[0][0]==0 and ex[-1][1]==size and all(a[1]==b[0]for a,b in zip(ex,ex[1:]))
        assert (V/copy).read_bytes()==(P/name).read_bytes()and(P/name).stat().st_size==size
        for s,e in ex[1:]:assert span(P/name,s,s+3)[:2]==b'##'or span(P/name,s,s+2)==b'# '
    assert (V/'history-r39-section.txt').read_bytes()==span(P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r39/308-positive-transfer.md',6297,7763)and(V/'history-r39-section.txt').read_bytes().startswith(b'## Operation-level attribution and decision\n')
    nav=read(V/'history-navigation.json');assert len(nav['eligible'])==1692 and nav['nonutf8']==12 and len(nav['hits'])==65
    for x in nav['hits']+nav['eligible']:assert not any(t in x['path'].casefold()for t in('r160','r161','r162','r193','r194','k369','t185','owner-recovery','arithmetic162','structural194','fresh-structural-discovery-r192','fresh-arithmetic-discovery-r159','r156'))
    for x in nav['eligible']:assert (P/x['path']).stat().st_size==x['bytes']
    # primary PDFs, extractions and page extents
    rc=[];fails=[]
    for f in('primary-receipts.json','primary-receipts-2.json','primary-receipts-3.json'):
        for x in read(V/f):(fails if 'error'in x else rc).append(x)
    assert [x['name']for x in rc]==['BSSWv2','Mathew2017','Hovey1993','BMR20261007','MNN2017','Mathew2016','DH2004','Heard2015v2']and [x['name']for x in fails]==['BMR','HMSv2']
    for x in rc:
        pdf=V/'primary'/(x['name']+'.pdf');assert pdf.stat().st_size==x['bytes']and sha(pdf)==x['sha256']and(V/'primary'/(x['name']+'.txt')).stat().st_size>0 and x['extract_exit']==0
    pr=lines(V/'primary-reading.jsonl');assert len(pr)==90
    pages=collections.defaultdict(set)
    for row in pr:
        t=V/'primary'/(row['name']+'.txt');assert hashlib.sha256(t.read_bytes()).hexdigest()==row['extract_sha256'];s,e=row['extent'];assert 0<=s<e<=t.stat().st_size;pages[row['name']].add(row['page'])
    assert set(pages)=={'BMR20261007','BSSWv2','Mathew2016','MNN2017','Heard2015v2','DH2004','Hovey1993'}and 'Mathew2017'not in pages
    assert pages['BMR20261007']==set(range(1,6))|set(range(34,38))|set(range(54,62))|set(range(82,101))and pages['DH2004']==set(range(8,11))|set(range(36,40))and pages['Heard2015v2']==set(range(8,16))and pages['Hovey1993']==set(range(17,22))
    assert sorted(p.name for p in(V/'primary/render').glob('*.png'))==['DH-37.png','DH-38.png','DH-39.png']and all(p.stat().st_size>0 for p in(V/'primary/render').glob('*.png'))
    # guards and the pre-traversal policy comparison required by the brief
    pol=read(V/'policy.json');W=set(pol['wildcards']);L=set(pol['literal_wildcards']);Tw=set(pol['no_r_twins'])
    assert len(L)==160 and len(Tw)==160 and len(W)==315 and len(set(pol['substrings']))==150 and L<=W and Tw<=W and pol['own_root']=='frontier/campaigns/2026-10-14/fresh-structural-discovery-r194'and {'publication','check'}<=set(pol['substrings'])
    assert {'*k369r134-*','*t185r144-*','*owner-recovery*','*s176a*','*arithmetic*r162*','*arithmetic*r156*','*structural*r193*','*structural*r194*','*structural*r200*','*analytic*r192*','*arithmetic*r165*'}<=L
    for w in L:
        tw=re.sub(r'\*r(\d+)',r'*\1',w,count=1)if re.search(r'\*r\d',w)else re.sub(r'r(\d{3}-)',r'\1',w,count=1)
        assert tw==w or tw in W,(w,tw)
    assert pol['comparison']=={'literal_count':160,'all_literals_present':True,'all_twins_present':True,'independent_expected_count':160}and pol['pretraversal_failure'].startswith('First extraction regex')
    briefw=set(re.findall(r'\*[a-z0-9*\-]+\*',(V/'brief.txt').read_text()));assert briefw<=W,briefw-W
    # controls: recorded results, then rerun on the intact baseline copy and on temporary copies
    ctl=read(V/'control-results.json');assert [(c['name'],c['expected_exit'],c['exit'])for c in ctl['controls']]==[('baseline',0,0),('wrong-detached-report-anchor',1,1),('changed-copy',1,1)]and ctl['mathematical_gate']is False
    assert ctl['originals_unchanged']['FINAL.md']==FINAL==sha(A/'FINAL.md')and ctl['originals_unchanged']['COMPARISON.md']==sha(A/'COMPARISON.md')
    bl=V/'controls/baseline';ba={n:sha(bl/n)for n in('FINAL.md','MANIFEST.json','REPORT.md')};assert ba['FINAL.md']==FINAL
    good=verifier(bl,ba['FINAL.md'],ba['MANIFEST.json'],ba['REPORT.md']);assert good.returncode==0 and json.loads(clean(good.stdout))==json.loads(ctl['controls'][0]['stdout'])=={'artifact_integrity':'verified','mathematical_gate':False,'selected_files':2}
    cc=V/'controls/changed-copy';ca={n:sha(cc/n)for n in('FINAL.md','MANIFEST.json','REPORT.md')};chg=verifier(cc,ca['FINAL.md'],ca['MANIFEST.json'],ca['REPORT.md']);assert chg.returncode==1 and clean(chg.stderr).strip()==ctl['controls'][2]['stderr'].strip()=='selected content mismatch: COMPARISON.md'
    wrong=verifier(bl,ba['FINAL.md'],ba['MANIFEST.json'],'0'*64);assert wrong.returncode==1 and clean(wrong.stderr).strip()==ctl['controls'][1]['stderr'].strip()=='detached anchor mismatch: REPORT.md'
    with tempfile.TemporaryDirectory()as td:
        t=Path(td)/'fx';shutil.copytree(bl,t);(t/'unlisted.txt').write_bytes(b'x');ex=verifier(t,ba['FINAL.md'],ba['MANIFEST.json'],ba['REPORT.md']);assert ex.returncode==1 and clean(ex.stderr).startswith('selection mismatch:')
        shutil.rmtree(t);shutil.copytree(bl,t);(t/'COMPARISON.md').unlink();mis=verifier(t,ba['FINAL.md'],ba['MANIFEST.json'],ba['REPORT.md']);assert mis.returncode==1 and clean(mis.stderr).startswith('selected file absent/outside root:')
        shutil.rmtree(t);shutil.copytree(bl,t);(t/'FINAL.md').write_bytes((bl/'FINAL.md').read_bytes()+b'\n');fin=verifier(t,ba['FINAL.md'],ba['MANIFEST.json'],ba['REPORT.md']);assert fin.returncode==1 and clean(fin.stderr).strip()=='detached anchor mismatch: FINAL.md'
    assert (cc/'COMPARISON.md').stat().st_size==3702 and(bl/'COMPARISON.md').stat().st_size==3680
    # --- Parent finite rechecks of the retained bookkeeping (not gates) ---
    rechecks=parent_rechecks()
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors['sha256'],'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':json.loads(clean(run.stdout)),'selected_files':147,'selected_bytes':22186011,'root_files':158,'detached_carriers':3,'control_files':8,'canonical_objects':85,'canonical_folders':5,'blobs_per_folder':blobs_per,'tree_entries_per_folder':entries_per,'canonical_folders_exhausted':True,'wrapper_anchors':[{'path':f+w,'bytes':nb,'git_blob':gb}for f,(w,nb,gb)in zip(FOLDERS,WRAPPERS)],'include_edges_reparsed':74,'nested_preamble_edges':4,'all_tex_bib_blobs_reached_from_wrappers':True,'wrapper_input_orders':wrapper_orders,'appendix_inputs':appendix,'source_text_objects_fully_read':80,'source_pdfs_authenticated_only':5,'display_ledger_rows':52,'chunk_display_rows':50,'recovery_rows':6,'direct_reads':['AGENTS.md','sources/upstream.json','NEW-TEN[4801,6347)'],'catalogue_extent_copied':[540867,544391],'completed_exception_copies_verified':6,'history_extents':17,'history_files_fully_partitioned':['i105 [0,31282)','i107 [0,39535)'],'history_r39_section':[6297,7763],'history_eligible_utf8':1692,'navigation_hits':65,'primary_pdfs':8,'primary_semantically_read':7,'primary_unread_download':['Mathew2017'],'primary_fetch_failures':[{'name':x['name'],'url':x['url'],'error':x['error']}for x in fails],'primary_page_rows':90,'renders_inspected':3,'controls_rerun':6,'guards':{'literal_wildcards':160,'no_r_twins':160,'wildcards':315,'substrings':150,'comparison':pol['comparison'],'brief_wildcards_all_installed':True,'pretraversal_regex_failure_disclosed':True},'child_calculations_rerun':[],'parent_exact_rechecks':rechecks,'parent_recheck_description':'Finite bookkeeping rechecks of the retained formulas, independent of the child text: the middle mapping matrix (2.3) from the splittings (2.1) and low stems (2.2); Gamma P (2.5) from the triangle with Gamma a vanishing by degrees, and its doubling to i105 Gamma F_4 computed two ways (W v U and C (x) P); the section 8 Adams-filtration inequalities p(p-4) and p^2-6p-1 over odd primes, failing exactly at p=3 (a=p) and p=3,5 (a=p+1); the section 6 row bookkeeping giving (6.1), the upper-line cofiber (6.2), the zeta transport between the degree 2r-1 and 2r-2 upper lines and the delta pair in degrees -3,-4 on the omega^0 line; and the sections 4-5 linear algebra that fib(psi-1)=0 iff psi-1 is invertible on random matrices over F_5, F_7 (so the two-term contraction exists while N is nonzero). These are not a proof review of the unpaid residual-cone vanishing or integral realization.','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, ANCHORS, verify_packet.py, DERIVATIONS (all nine sections), COMPARISON and private/READING-LIMITS.md; INTERFACES.md by structure only; private record schemas, acquire.py, read_source.py, history_select.py, run_controls.py and seal_packet_once.py. Source318 (80 text objects) and primary (BMR 2026-10-07, DH 2004, BSSW v2, MNN 2017, Mathew 2016, Hovey 1993, Heard 2015 v2) operative reading is attributed to the child, not fresh parent protected-body reading. Live Arithmetic162c (other parent thread) not inspected.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['selected_files','root_files','canonical_objects','blobs_per_folder','include_edges_reparsed','completed_exception_copies_verified','history_extents','primary_pdfs','controls_rerun','parent_exact_rechecks','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
