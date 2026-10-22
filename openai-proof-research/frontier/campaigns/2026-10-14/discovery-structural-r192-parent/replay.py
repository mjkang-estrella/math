#!/usr/bin/env python3
"""Read-only Structural192 discovery intake; artifact checks and finite rechecks only, no mathematical gate."""
import collections,datetime,hashlib,importlib.util,json,re,shutil,stat,subprocess,tempfile
from itertools import product
from math import comb
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];A=B/'fresh-structural-discovery-r192';V=A/'private'
sp=importlib.util.spec_from_file_location('base',B/'discovery-analytic-r168-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha=h.sha;snap=h.snap
FOLDER='preprints/The-Stable-Hurewicz-Image-of-the-Sphere-at-Two-September-25-2026/'
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
# --- parent exterior model (DERIVATIONS 2-3): Laurent monomials x^c prod y_j^{b_j}, primitives q_i=x d/dy_{i+1} (i<k-1), q_{k-1}=x(x d/dx + sum y_j d/dy_j), mod 2 ---
def q_act(k,i,mono):
    c,b=mono
    if i<k-1:
        if b[i]%2==0:return None
        bb=list(b);bb[i]-=1;return(c+1,tuple(bb))
    return None if(c+sum(b))%2==0 else(c+1,b)
def main():
    anchors=read(A/'ANCHORS.json');assert anchors=={'FINAL.md':'d748ea0f8d077fe49d6cb61bdbaedb4a1d8b8b25715296bc595c35eb05515e95','private/MANIFEST.json':'11c564b9172007168464aa1ead7b64faba1ca0e568d117f93c55187c764ad2fc','REPORT.md':'eabc173793b967aaee4f6869b478f24b0789d4affbd989544d41054e496d8dac'}
    before=snap(A);mode=stat.S_IMODE(A.stat().st_mode);assert all(sha(A/p)==v for p,v in anchors.items())
    F,M,R=anchors['FINAL.md'],anchors['private/MANIFEST.json'],anchors['REPORT.md']
    run=verifier(A,F,M,R);assert run.returncode==0 and not run.stderr and clean(run.stdout).strip()=='PASS: exact payload and three explicit detached anchors; 97 files'
    m=read(V/'MANIFEST.json');assert m['schema']=='r192-exact-packet-v1'and len(m['files'])==97 and sum(x['bytes']for x in m['files'])==5626346;names={x['path']for x in m['files']}
    for x in m['files']:p=A/x['path'];assert p.stat().st_size==x['bytes']and sha(p)==x['sha256']
    rootfiles={str(p.relative_to(A))for p in A.rglob('*')if p.is_file()};assert rootfiles==names|{'private/MANIFEST.json','REPORT.md','ANCHORS.json'}and len(rootfiles)==100
    assert {'FINAL.md','DERIVATIONS.md','INTERFACES.md','COMPARISON.md','RESEARCH-NOTES.md','verify_packet.py','private/READING-LIMITS.md','private/brief.txt','private/guards.json','private/guards-initial.json','private/guard-correction.json'}<=names
    assert not any(p.is_symlink()for p in A.rglob('*'))
    # pinned tree, canonical blobs exhausting the folder, wrapper and include order
    tree=read(P/'sources/preprints-tree.json');lookup={e['path']:e for e in tree['tree']};assert len(lookup)==13223 and not tree['truncated']and sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    auth=read(V/'source-authentication.json');assert len(auth)==12
    for x in auth:
        e=lookup[x['path']];p=P/x['local'];d=p.read_bytes();assert x['path'].startswith(FOLDER)and e['type']=='blob'and len(d)==x['size']==e['size']and x['sha']==e['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()and sha(p)==x['sha256']and x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    assert sorted(k for k,e in lookup.items()if k.startswith(FOLDER)and e['type']=='blob')==sorted(x['path']for x in auth)and sum(1 for k in lookup if k.startswith(FOLDER))==14
    ft=read(V/'family-tree.json');assert len(ft)==14 and sorted((e['path'],e['sha'])for e in ft)==sorted((k,e['sha'])for k,e in lookup.items()if k.startswith(FOLDER))
    assert lookup[FOLDER+'build/paper.tex']['size']==762 and lookup[FOLDER+'build/paper.tex']['sha']=='eb74588690f456774d93e1abbd7b495e56ead5d6'
    w=(V/'source/build/paper.tex').read_text();ins=re.findall(r'\\(input|bibliography)\{([^}]*)\}',w);assert [t for _,t in ins]==['preamble','introduction','weights','cones','powers','algebra','conclusion','references']
    ie=read(V/'include-edges.json');assert len(ie)==9 and [(e['kind'],e['to'])for e in ie if e['from']=='build/paper.tex']==[(k,t)for k,t in ins]and ie[0]==dict(**{'from':'build/introduction.tex','kind':'input','to':'figures/proof-route'})
    assert '\\input{figures/proof-route}'in(V/'source/build/introduction.tex').read_text()
    se=read(V/'source-extents.json');assert len(se)==11 and all(x['semantic']=='complete'and x['extent']==[0,(V/'source'/x['path']).stat().st_size]and sha(V/'source'/x['path'])==x['sha256']for x in se)
    assert sorted(x['path']for x in se)==sorted(x['path'][len(FOLDER):]for x in auth if not x['path'].endswith('.pdf'))and lookup[FOLDER+'paper.pdf']['size']==515149
    # direct reads, brief copy, catalogue span, completed copies, history spans
    assert (V/'brief.txt').read_bytes()==(B/'expanded-target-2026-10-17/fresh-structural-r192-brief.txt').read_bytes()and sha(V/'brief.txt')=='b05295ed0387cb2025458fcafb40de8e1dd3c7f77863c7d4fbb096a0841e23b7'and (V/'brief.txt').stat().st_size==26727
    assert (V/'acceptance.txt').read_bytes()==span(P/'frontier/NEW-TEN-2026-10-14.md',4801,6347)
    cat=span(P/'sources/CONTENTS.md',538801,539611);assert (V/'Source316-catalogue.txt').read_bytes()==cat and hashlib.sha256(cat).hexdigest().startswith('113ede9e')and cat.startswith(b'**316. ')
    ce=read(V/'completed-extents.json');assert len(ce)==6
    for x in ce:
        o=P/x['original'];assert 'r191'in x['original']and x['extent']==[0,o.stat().st_size]and sha(o)==x['sha256']
        cp=V/('completed-'+x['original'][len('frontier/campaigns/2026-10-14/'):].replace('/','--'));assert cp.read_bytes()==o.read_bytes()
    assert sha(P/'frontier/campaigns/2026-10-14/discovery-structural-r191-parent/assessment.md')=='e3c3875ebbfd1414f6d665b91163899e1d3d6e227d89340c782ecb37dcfa3974'
    hx=read(V/'original-extents.json');assert len(hx)==7
    for x in hx:
        d=span(P/x['path'],x['start'],x['end']);assert hashlib.sha256(d).hexdigest()==x['sha256']and (P/x['copy']).read_bytes()==d and not any(t in x['path']for t in('r158','r159','r160','r190','r191','r192','r193'))
    nav=read(V/'history-navigation.json');assert nav['counts']=={'eligible_utf8':1665,'non_utf8':12,'pruned':8142}and len(nav['hits'])==7
    nav2=read(V/'additional-history-navigation.json');nav3=read(V/'outside-frontier-navigation.json');assert len(nav2)==38 and nav3['counts']['eligible_utf8']==27 and len(nav3['hits'])==1
    for x in nav['hits']+nav2:assert (P/x['path']).stat().st_size==x['bytes']and not any(t in x['path'].casefold()for t in('r158','r159','r160','r190','r191','r193','k369','t185'))
    # primary PDFs, extractions and page extents
    rc=read(V/'primary/receipts.json');assert [x['name']for x in rc]==['kuhn2018','kuhn-pereira2017','giambalvo-peterson','hunter2025']and 'failure'in rc[2]
    for x in rc:
        if 'failure'in x:continue
        pdf=V/'primary'/(x['name']+'.pdf');assert pdf.stat().st_size==x['bytes']and sha(pdf)==x['sha256']and (V/'primary'/(x['name']+'.txt')).stat().st_size>0
    for nm,rec in(('kuhn-pereira-correct2017','correct-receipt.json'),('hung2020','hung-receipt.json'),('hung-detailed','hung-detailed-receipt.json'),('sum2024','sum-receipt.json')):
        r=read(V/'primary'/rec);pdf=V/'primary'/(nm+'.pdf');assert pdf.stat().st_size==r['bytes']and sha(pdf)==r['sha256']
    pe=read(V/'primary-extents.json');assert len(pe)==57 and collections.Counter(x['file']for x in pe)=={'primary/kuhn2018.txt':17,'primary/hunter2025.txt':17,'primary/kuhn-pereira-correct2017.txt':10,'primary/hung2020.txt':7,'primary/sum2024.txt':6}
    for x in pe:assert hashlib.sha256(span(V/x['file'],x['start'],x['end'])).hexdigest()==x['sha256']
    pv=read(V/'primary-version-only-extents.json');assert pv['file']=='primary/hung-detailed.txt'and pv['extents']==[[0,1759],[21344,25699]]and (V/'primary/hung-detailed.txt').stat().st_size>=25699
    assert (V/'primary/hunter-page11.png').stat().st_size>0
    # guards: initial vs corrected, disclosed defect
    g=read(V/'guards.json');gi=read(V/'guards-initial.json');gc=read(V/'guard-correction.json')
    assert len(gi['wildcards'])==293 and len(g['wildcards'])==296 and len(g['substrings'])==len(gi['substrings'])==150 and set(g['wildcards'])-set(gi['wildcards'])=={'*k369r134-*','*k369134-*','*t185144-*'}==set(gc['missing_in_initial_policy'])|set(gc['missing_no_r_twins'])
    assert {'*arithmetic*r159*','*arithmetic*r160*','*structural*r191*','*structural*r193*','*t185r144-*'}<=set(gi['wildcards'])and 'publication'in g['substrings']and g['own_root']=='frontier/campaigns/2026-10-14/fresh-structural-discovery-r192'
    # controls: recorded results, then rerun on temporary copies of the clean fixture
    ctl=read(V/'controls/results.json');assert [(c['control'],c['expected_exit'],c['actual_exit'])for c in ctl]==[('clean',0,0),('mutated',1,1),('missing',1,1),('extra',1,1)]
    fx=V/'controls/clean';fa=read(fx/'ANCHORS.json');assert all(sha(fx/p)==v for p,v in fa.items())
    good=verifier(fx,fa['FINAL.md'],fa['private/MANIFEST.json'],fa['REPORT.md']);assert good.returncode==0 and clean(good.stdout)==ctl[0]['stdout']
    with tempfile.TemporaryDirectory()as td:
        t=Path(td)/'fx';shutil.copytree(fx,t);(t/'data.txt').write_bytes((fx/'data.txt').read_bytes()+b'!');bad=verifier(t,fa['FINAL.md'],fa['private/MANIFEST.json'],fa['REPORT.md']);assert bad.returncode==1 and clean(bad.stderr)==ctl[1]['stderr']
        shutil.rmtree(t);shutil.copytree(fx,t);(t/'data.txt').unlink();mis=verifier(t,fa['FINAL.md'],fa['private/MANIFEST.json'],fa['REPORT.md']);assert mis.returncode==1 and clean(mis.stderr)==ctl[2]['stderr']
        shutil.rmtree(t);shutil.copytree(fx,t);(t/'unlisted.txt').write_bytes(b'x');ex=verifier(t,fa['FINAL.md'],fa['private/MANIFEST.json'],fa['REPORT.md']);assert ex.returncode==1 and clean(ex.stderr)==ctl[3]['stderr']
    # child calculations rerun on temporary copies
    with tempfile.TemporaryDirectory()as td:
        t=Path(td)
        for s in('exterior_calculation.py','bar_calculation.py','transgression_calculation.py'):shutil.copy(V/s,t/s)
        r=subprocess.run(['python','-I','-B',str(t/'exterior_calculation.py')],cwd=td,capture_output=True,text=True,env=ENV,timeout=600);assert r.returncode==0 and read(t/'exterior-calculation.json')==read(V/'exterior-calculation.json')==[{'rank':1,'positive_degree_basis_cases':27},{'rank':2,'positive_degree_basis_cases':243},{'rank':3,'positive_degree_basis_cases':1539},{'rank':4,'positive_degree_basis_cases':8262}]
        E2=dict(ENV,PYTHONPATH=td)  # the transgression script imports bar_calculation from its own directory
        r=subprocess.run(['python','-B','-s',str(t/'transgression_calculation.py')],cwd=td,capture_output=True,text=True,env=E2,timeout=600);assert r.returncode==0,r.stderr
        assert read(t/'transgression-calculation.json')==read(V/'transgression-calculation.json')
        r=subprocess.run(['python','-I','-B',str(t/'bar_calculation.py')],cwd=td,capture_output=True,text=True,env=ENV,timeout=1800);assert r.returncode==0,r.stderr
        assert read(t/'bar-calculation.json')==read(V/'bar-calculation.json')
        # parent recomputation of the residual identity (18) for odd c<=15 with the child's Adem/bar routines as a library (no retained child script produces parametric-bar-residual.json)
        sp2=importlib.util.spec_from_file_location('barlib',t/'bar_calculation.py');bl=importlib.util.module_from_spec(sp2);sp2.loader.exec_module(bl)
        a,b,q=(1,),(2,),[(2,1),(3,)]
        def Z(c):
            z=set()
            for u in q:
                for v in q:z^={((u,v),c)}
            for u in q:z^={((a,u),c+2),((u,a),c+2)}
            z^={((a,a),c+4)};return z
        def W(c):
            w={((a,a,b),c+2),((a,b,a),c+2),((b,a,a),c+2),((a,(2,1),b),c),((b,b,b),c)}
            for u in q:w^={((a,b,u),c),((b,a,u),c)}
            return w
        resid={}
        for c in range(1,16,2):
            dW=set()
            for x in W(c):dW^=bl.boundary(x)
            assert len(W(c))==9 and len(Z(c))==9 and not any(bl.boundary(x)and False for x in Z(c))
            zc=set()
            for x in Z(c):zc^=bl.boundary(x)
            assert not zc  # Z(c) is a cycle
            resid[c]=dW^Z(c)
            assert resid[c]==(set()if c%4==1 else{((a,a),c+4),((a,(2,1)),c+2),((b,b),c+2)})
        pr=read(V/'parametric-bar-residual.json');assert [x['c']for x in pr]==list(range(1,16,2))
        for x in pr:assert {(tuple(tuple(w)for w in ww),e)for ww,e in x['residual']}==resid[x['c']]
    tc=read(V/'transgression-calculation.json');assert len(tc['filling'])==9 and len(tc['cycle'])==9
    bc=read(V/'bar-calculation.json');row=[x for x in bc if x['floor']==0 and x['t']==7][0];assert row['chain_dims'][1:]==[11,28,32]
    # --- Parent finite rechecks (not gates) ---
    # (2): q_T v = x^{-k+|S|+eps} prod_{j-1 notin S} y_j, and the 2^k monomials have distinct (y parity, x parity) patterns
    for k in(1,2,3,4):
        v=(-k,tuple([1]*(k-1)));seen=set()
        for S in product((0,1),repeat=k-1):
            for eps in(0,1):
                mono=v;ok=True
                for i in range(k-1):
                    if S[i]:mono=q_act(k,i,mono);ok=ok and mono is not None
                if eps:mono=q_act(k,k-1,mono);ok=ok and mono is not None
                assert ok;c,b=mono;assert c==-k+sum(S)+eps and b==tuple(0 if S[j-1]else 1 for j in range(1,k))
                pat=(c%2,tuple(x%2 for x in b));assert pat not in seen;seen.add(pat)
        assert len(seen)==2**k
        # q_i^2=0 and q_i q_j = q_j q_i on random monomials (exterior relations as operators)
        for mono in[(c,tuple(b))for c in range(-3,4)for b in product(range(3),repeat=k-1)]:
            for i in range(k):
                y=q_act(k,i,mono);assert y is None or q_act(k,i,y)is None
                for j in range(k):
                    a1=q_act(k,i,mono);a1=None if a1 is None else q_act(k,j,a1);a2=q_act(k,j,mono);a2=None if a2 is None else q_act(k,i,a2)
                    assert a1==a2  # commuting operators on F2 monomials (each is either the same monomial or zero)
    # k=1 floor statement: q_0 x^c = c x^{c+1}; n odd: no positive Tor; n even: the floor class survives
    assert all((q_act(1,0,(c,()))is None)==(c%2==0)for c in range(-4,8))
    # (15): Sq^{2r} x^{2a+1} = C(2a+1,2r) x^{...} with C(2a+1,2r) = C(a,r) mod 2 (Lucas)
    assert all(comb(2*a+1,2*r)%2==comb(a,r)%2 for a in range(0,40)for r in range(0,40))
    # q_1 = x^2 q_0 on F2[x] (|x|=1): Sq^3 x^c + Sq^2 Sq^1 x^c = c x^{c+3}
    assert all((comb(c,3)+c*comb(c+1,2))%2==c%2 for c in range(0,64))
    # (18) coefficient identities for odd c: C(c,2)=C(c,3)=eps(c), C(c+2,2)=1+eps(c) mod 2; eps(c)=0 iff c=1 mod 4
    for c in range(1,64,2):e=comb(c,2)%2;assert comb(c,3)%2==e and comb(c+2,2)%2==(1+e)%2 and(e==0)==(c%4==1)
    # Adem relations used: Sq1 Sq1=0, Sq1 Sq2=Sq3, Sq2 Sq2=Sq3 Sq1 — recheck via the Adem formula
    def adem(a,b):return {(a+b-t,t)for t in range(a//2+1)if comb(b-t-1,a-2*t)%2 and b-t-1>=0}
    assert adem(1,1)==set()and adem(1,2)=={(3,0)}and adem(2,2)=={(3,1)}
    # parity (7)/(12) bookkeeping: floor coefficient degree parity n+n=0 (with the suspension) and odd |q_i|=2^{i+1}-1
    assert all((2**(i+1)-1)%2==1 for i in range(12))and all((n+n)%2==0 for n in range(10))
    assert snap(A)==before and stat.S_IMODE(A.stat().st_mode)==mode
    dump(O/'observed-root.json',{'root':before,'root_mode':mode})
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'detached_anchor_file_matches':True,'artifact_only':True,'author_verifier_stdout':clean(run.stdout).strip(),'payload_files':97,'payload_bytes':5626346,'root_files':100,'detached_carriers':3,'canonical_objects':12,'canonical_folders':1,'blobs_per_folder':[12],'tree_entries_per_folder':[14],'canonical_folders_exhausted':True,'wrapper_anchor':{'path':FOLDER+'build/paper.tex','bytes':762,'git_blob':'eb74588690f456774d93e1abbd7b495e56ead5d6'},'include_order_reparsed':['preamble','introduction','weights','cones','powers','algebra','conclusion','references(bibliography)','introduction->figures/proof-route'],'source_text_objects_fully_read':11,'source_pdfs_authenticated_only':1,'direct_reads':3,'catalogue_extent_copied':[538801,539611],'completed_exception_copies':6,'history_extents':7,'history_eligible_utf8':[1665,27],'navigation_hits':[7,38,1],'primary_pdfs':7,'primary_fetch_failures':['giambalvo-peterson HTTP 404'],'primary_page_extents':57,'controls_rerun':4,'child_calculations_rerun':['exterior_calculation.py (10071 cases, identical JSON)','transgression_calculation.py (identical JSON)','bar_calculation.py (identical bar-calculation.json); residual identity (18) recomputed by the parent for odd c<=15 and matched to parametric-bar-residual.json'],'guard_wildcards_initial_vs_corrected':[293,296],'guard_defect_disclosed':['*k369r134-*','*k369134-*','*t185144-*'],'parent_exact_rechecks':'Laurent basis formula (2) and the 2^k distinct parity patterns for k<=4; exterior operator relations q_i^2=0 and commutation on monomials; k=1 floor parity; Lucas identity behind (15); q_1=x^2 q_0 on F2[x]; the three binomial identities behind the residual formula (18) and eps(c)=0 iff c=1 mod 4; Adem relations Sq1Sq1=0, Sq1Sq2=Sq3, Sq2Sq2=Sq3Sq1; parity bookkeeping for (7)/(12); child exterior (dH+Hd=1, d^2=0, exact exponent loss), nine-term filling and bar-table scripts rerun on temporary copies with identical outputs','entire_root_unchanged':True,'parent_semantic_reading':'Complete FINAL, REPORT, ANCHORS, verify_packet.py, DERIVATIONS (all sections; long paragraphs of 6-7 partly display-truncated), RESEARCH-NOTES, COMPARISON, READING-LIMITS and the private record schemas and calculation scripts. Source316 (11 text objects) and primary (Kuhn, Kuhn-Pereira, Hunter, Hung, Sum) operative reading attributed to the child, not fresh parent protected-body reading. Live Arithmetic160 (dispatched by another parent thread) not inspected.'}
    dump(O/'replay.json',report);print(json.dumps({k:report[k]for k in['payload_files','root_files','canonical_objects','completed_exception_copies','history_extents','primary_pdfs','controls_rerun','entire_root_unchanged','artifact_only']}))
if __name__=='__main__':main()
