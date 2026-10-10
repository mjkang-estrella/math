"""One-time I68 evidence indexing. Writes only the assigned I68 source directory.

This is an acquisition helper, NOT the read-only verifier. No old seals change.
"""
from pathlib import Path
import hashlib, json, re
from datetime import datetime, timezone

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i68_logarithmic_blowup_novelty'
OLD=ROOT/'frontier/sources/i66_dispersive_equation_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def write(name,obj):(S/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def rel(p):return str(p.relative_to(ROOT))

def capture():
    refs=read(S/'references.json')
    known={x['path'] for x in refs}
    for path in ['frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md',
                 'frontier/reviews/i58-standard-map-additive-entropy-novelty.md',
                 'frontier/reviews/i56-sharp-entropy-stability-novelty.md']:
        if path not in known:
            b=(ROOT/path).read_bytes()
            refs.append({'path':path,'bytes':len(b),'sha256':sha(b),'mutable':False})
    write('references.json',refs)
    # Peer work was concurrent. Freeze the observed report, not an assertion that
    # a possibly unfinished live peer path has become immutable.
    peer=ROOT/'frontier/reviews/i67-logarithmic-blowup-r2.md'
    b=peer.read_bytes(); snap=S/'i67-observed-report.md';snap.write_bytes(b)
    write('i67-observation.json',{'observed_utc':datetime.now(timezone.utc).isoformat(),
          'live_path':rel(peer),'snapshot':rel(snap),'sha256':sha(b),'bytes':len(b),
          'observed_verdict':'PASS ORIGINAL WITHOUT REPAIRS',
          'peer_seal_present_at_observation':(ROOT/'frontier/sources/i67_logarithmic_blowup_r2/seal.json').exists(),
          'scope':'Observation of a separately authored report; no assertion that its evidence verifier has passed.'})
    pins=read(OLD/'pinned-manifest.json')
    bylocal={x['local']:x for x in pins}
    B=OLD/'pinned/preprints/Stable-Self-Similar-Blowup-for-a-Supercritical-Defocusing-Schrodinger-Equation-on-the-Torus-September-24-2026/build'
    passages=[]
    def passage(label,path,start,end,purpose,url=None):
        lines=path.read_bytes().splitlines(keepends=True)
        assert 1<=start<=end<=len(lines),(label,len(lines))
        b=b''.join(lines[start-1:end]);key=rel(path)
        p={'label':label,'path':key,'start_line':start,'end_line':end,
           'purpose':purpose,'sha256':sha(b),'text':b.decode()}
        if key in bylocal:
            p.update({k:bylocal[key][k] for k in ['url','git_blob']})
        elif url:p['url']=url
        passages.append(p)
    for name,ranges in {
       'profiles.tex':[(1,146,'profile theorem, amplitude equation, uniform exterior pressure'),
                       (148,333,'boundary gap and full inner-barrier proof'),
                       (334,374,'complete compact core-limit proof'),
                       (388,549,'complete exterior construction and uniform tails'),
                       (551,744,'matching and remaining profile estimates')],
       'linear.tex':[(1,208,'norm, zero mode, algebra, localization, generator interfaces'),
                     (324,608,'semigroup decay, torus transfer and strong continuity')],
       'nonlinear.tex':[(1,123,'cutoff forcing and full finite-slab estimates'),
                        (125,214,'forward/backward graph and continuity proof'),
                        (215,336,'full physical-parameter degree and continuation proof')],
       'spectrum.tex':[(1,125,'classification and spectral proof interface')]
    }.items():
        for start,end,purpose in ranges:passage('B-'+name+'-'+str(start),B/'sections'/name,start,end,purpose)
    passage('B-main-theorem',B/'main.tex',55,130,'full quantified source theorem')
    old_primary=[
      ('buck-html.txt','2609.23685v1',890,1100,'spectral localization and complete Proposition 4.8 graph proof'),
      ('li-html.txt','2304.02078v2',51,138,'focusing hypotheses and theorem scope'),
      ('li-html.txt','2304.02078v2',1864,1932,'complete §6.3 symmetry/Brouwer matching'),
      ('cao-html.txt','2410.04532v1',170,267,'periodic dimension eight scaling and damped cutoff'),
      ('cao-html.txt','2410.04532v1',937,944,'complete §3.7 topological selection'),
      ('wallauch-v1-html.txt','2006.04600v1',152,210,'strict q<p perturbation hypotheses'),
      ('wallauch-v1-html.txt','2006.04600v1',674,789,'complete perturbation estimate Lemma 3.2'),
      ('wallauch-v1-html.txt','2006.04600v1',914,1064,'complete phase modulation and positive-mode correction'),
      ('wallauch-v1-html.txt','2006.04600v1',1065,1147,'physical time parameter selection')]
    for name,version,start,end,purpose in old_primary:
        passage(name+'-'+str(start),OLD/'primary'/name,start,end,purpose,'https://arxiv.org/html/'+version)
    new_primary=[
      ('nguyen-v4.txt','1406.5233v4',35,223,'exact logarithmic perturbation, theorem scope and modified profile'),
      ('nguyen-v4.txt','1406.5233v4',345,410,'finite dimensional reduction, transversality and degree'),
      ('nguyen-v4.txt','1406.5233v4',441,536,'full small-amplitude split, amplitude formula and potential cancellation proof'),
      ('nguyen-v4.txt','1406.5233v4',675,750,'complete profile-remainder calculation'),
      ('nguyen-ode-v4.txt','1404.4018v4',47,63,'earlier companion PDE requires logarithmic exponent greater than one'),
      ('nguyen-ode-v4.txt','1404.4018v4',966,1021,'full antecedent amplitude ODE proof, Lemmas A.1–A.3'),
      ('nguyen-analysis-v1.txt','1410.4079v1',649,699,'later companion repeats amplitude lemma and cancellation'),
      ('hamza-v1.txt','1311.7479v1',40,100,'subconformal wave and logarithmic exponent greater than one'),
      ('bento-v2.txt','1007.5039v2',110,265,'actual nonautonomous theorem hypotheses'),
      ('bento-v2.txt','1007.5039v2',575,636,'integral graph contraction proof'),
      ('lecoz-v1.txt','1406.6002v1',178,405,'complete Proposition 3 profile corrections and remainder proof')]
    for name,version,start,end,purpose in new_primary:
        passage(name+'-'+str(start),S/'primary'/name,start,end,purpose,'https://arxiv.org/html/'+version)
    write('passages.json',passages)
    raw=[]
    for name in ['profiles','linear','nonlinear']:
        p=S/'primary'/('pin-'+name+'.tex');pin=bylocal[rel(B/'sections'/(name+'.tex'))]
        assert p.read_bytes()==(ROOT/pin['local']).read_bytes()
        raw.append({'path':rel(p),'pinned_local':pin['local'],'source':pin['path'],
                    'sha256':sha(p.read_bytes()),'git_blob':pin['git_blob'],'url':pin['url']})
    write('raw-pin-comparisons.json',raw)
    versions=[]
    for p in sorted((S/'primary').glob('*-abs.html')):
        html=p.read_text();m=re.search(r'<meta property="og:url" content="https://arxiv.org/abs/([^\"]+)"',html)
        assert m,p
        text=p.with_suffix('.txt').read_text()
        lines=[x for x in text.splitlines() if 'Submitted on' in x or 'for this version)' in x]
        versions.append({'abstract_html':rel(p),'abstract_text':rel(p.with_suffix('.txt')),
                        'current_version_at_retrieval':m[1],'version_passage':lines,
                        'abstract_sha256':sha(p.read_bytes())})
    write('current-versions.json',versions)
    groups=[
       {'queries':['nonlinear Schrodinger blow up logarithmic perturbation non homogeneous nonlinearity self similar',
                   'wave equation strong perturbation logarithmic nonlinearity stable blow up Hamza Zaag Nguyen',
                   'nonautonomous stable manifold polynomial decay neutral mode Lyapunov Perron'],
        'raw_results':None},
       {'queries':['Schrodinger blowup "logarithmic perturbation"','Schrodinger blow up "nonhomogeneous" nonlinearity',
                   'stable blow up "strongly perturbed" logarithmic Nguyen Zaag','nonuniform polynomial dichotomy stable manifolds Barreira Valls'],
        'raw_results':'web-search-2.json'},
       {'queries':['Schrodinger blowup "log" "nonlinearity" "perturbation" -site:reddit.com -site:wikipedia.org',
                   '"Schrödinger" "nonhomogeneous nonlinearity" blowup','"Schrödinger" "logarithmically" "blow-up"',
                   '"Schrödinger" "non-scaling invariant" blow'],
        'domains_for_first_query':['arxiv.org'],'raw_results':'web-search-3.json'},
       {'queries':['Le Coz Martel Raphael minimal mass blow up double power nonlinear Schrödinger arxiv',
                   '"Schrodinger" "log" "perturbations" "blowup" stability',
                   '"Schrödinger" "general nonlinearities" "blow-up" Merle Raphael'],
        'raw_results':'web-search-4.json'},
       {'queries':['"Nguyen" "On the blow-up results for a class of strongly perturbed" heat equation',
                   '"Nguyen" "Lemma A.3" "strongly perturbed"'], 'raw_results':None}]
    write('web-search-scope.json',{'retrieval_day_utc':'2026-10-10','groups':groups,
       'limits':'Finite English-language query sets, no exhaustive citation or worldwide-priority search. Domains unrestricted unless specified. Nonprimary results are discovery leads only. Null raw_results means no raw tool response archived; actual primary retrieval bytes remain independently preserved. Full corpus domain is fixed separately in searches.json.'})

if __name__=='__main__':capture()
