"""One-time new I70 passage/result archive. Refuses to overwrite its products."""
from pathlib import Path
import hashlib,json,re,runpy
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i70_symplectic_geometry_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(name,x):
    p=OUT/name
    if p.exists():raise RuntimeError('Refusing refresh '+name)
    p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
    passages=[]
    def add(path,ranges,purpose):
        p=OUT/path;b=p.read_bytes();lines=b.decode().splitlines(keepends=True)
        for lo,hi in ranges:
            hi=min(hi or len(lines),len(lines));assert 1<=lo<=hi
            text=''.join(lines[lo-1:hi])
            passages.append(dict(path=path,first_line=lo,last_line=hi,purpose=purpose,
                                 file_sha256=sha(b),text=text,passage_sha256=sha(text.encode())))
    P='pinned/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/build/sections/'
    for f,ranges,why in [
      ('introduction.tex',[(1,None)],'Absolute theorem, conventions and roadmap'),
      ('comparison.tex',[(1,230),(234,334),(336,460)],'Actual comparison, contraction, planar construction and lifting interfaces'),
      ('surface.tex',[(1,110),(124,230),(305,432)],'Relative model hypotheses, exact paths, one-covector positivity and outer faces'),
      ('geometry.tex',[(1,95),(432,515)],'Same-complex Kähler Moser and standard shell'),
      ('applications.tex',[(215,245),(434,482)],'Large-ball slack and actual centered-shell endpoint'),
      ('sixdim.tex',[(743,878)],'Six-dimensional large-ball moment-preserving transfer endpoint')]:add(P+f,ranges,why)
    W='pinned/preprints/Symplectic-Balls-in-Symmetric-Polar-Products-September-22-2026/build/sections/'
    for f,ranges in [('introduction.tex',[(1,None)]),('ball.tex',[(1,85)]),('realization.tex',[(1,151)]),('approximation.tex',[(1,None)])]:add(W+f,ranges,'Polar-product statement and paid construction/approximation/packing interfaces')
    L='pinned/preprints/A-counterexample-to-the-nearby-Lagrangian-conjecture-September-23-2026/build/sections/'
    for f,ranges in [('introduction.tex',[(1,None)]),('tubes.tex',[(1,None)]),('embedding.tex',[(1,118)]),('obstruction.tex',[(1,None)]),('transport.tex',[(136,204),(474,543)])]:add(L+f,ranges,'Kernel class, exact embedding, zero-section obstruction and transport interfaces')
    for title,files in [
      ('Hamiltonian-Fixed-Points-Below-the-Stable-Morse-Number-October-5-2026',['introduction','counts']),
      ('Hamiltonian-Fixed-Points-Below-the-Stable-Morse-Number-in-Dimension-Twenty-Two-October-5-2026',['introduction','counts','dynamics']),
      ('Sharpness-of-the-Cyclic-Integral-Floer-Bound-Below-the-Stable-Morse-Number-October-5-2026',['introduction','construction'])]:
        for f in files:add(f'pinned/preprints/{title}/build/sections/{f}.tex',[(1,None)],'Fixed-point theorem and its actual lower operations')
    add('pinned/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/build/sections/introduction.tex',[(18,90)],'Already stronger equality companion')
    add('pinned/preprints/Maximal-Multipoint-Seshadri-Constants-in-Higher-Dimensions-October-5-2026/build/sections/introduction.tex',[(1,120)],'Very-general algebraic tuple versus given symplectic blowup')
    add('pinned/preprints/A-degenerate-counterexample-to-the-critical-number-Arnold-bound-September-23-2026/build/sections/00-introduction.tex',[(1,None)],'Distinct degenerate theorem and finite-order operation')
    add('pinned/preprints/A-degenerate-counterexample-to-the-critical-number-Arnold-bound-September-23-2026/build/sections/01-reduction.tex',[(1,110)],'Finite-order short-period interface')
    add('pinned/preprints/A-nondegenerate-counterexample-to-the-Morse-number-Arnold-bound-September-23-2026/build/sections/01-introduction.tex',[(1,None)],'Ordinary Morse counterexample and fixed eight-variable construction')
    add('pinned/preprints/A-nondegenerate-counterexample-to-the-Morse-number-Arnold-bound-September-23-2026/build/sections/05-hamiltonian.tex',[(1,90)],'Cap-transfer scope and short-period operation')
    for name,ranges,why in [
      ('2312.13224v1',[(70,122)],'Conjecture A versus stabilized theorem B'),
      ('2509.15390v1',[(66,102)],'Stability versus asymptotic filling and limiting-embedding qualification'),
      ('1404.4183v1',[(44,103)],'Strong stability, dimension and curve-placement interfaces'),
      ('2209.08599v1',[(180,198)],'Actual cyclic integral lower bound'),
      ('2606.15847v1',[(335,335),(480,501)],'Current PSS/isomorphism and cyclic bound'),
      ('2603.28007v2',[(102,155),(507,539)],'Natural torsion coset versus arbitrary generating family'),
      ('2011.03317v2',[(537,602)],'Four-dimensional connectivity and the inflation step')]:add('primary/'+name+'-html.txt',ranges,why)
    write('passages.json',passages)
    versions=[]
    for p in sorted((OUT/'primary').glob('*-abs.body')):
        arxiv=p.name[:-9];txt=p.read_text();vs=re.findall(re.escape(arxiv)+r'v(\d+)',txt)
        version=max(map(int,vs));lines=(p.with_suffix('.txt')).read_text().splitlines()
        idx=next(i for i,l in enumerate(lines) if 'Submission history' in l)
        versions.append(dict(arxiv=arxiv,latest_observed=version,abs_body='primary/'+p.name,
          versioned_body=f'primary/{arxiv}v{version}-html.body',
          history_first_line=idx+1,history_lines=lines[idx:idx+15],
          abs_sha256=sha(p.read_bytes())))
    write('current-versions.json',versions)
    diag=runpy.run_path(str(ROOT/'frontier/experiments/i70_symplectic_geometry_discovery/diagnostics.py'))['run']()
    write('diagnostic-results.json',diag)
    write('web-search-scope.json',dict(
      first_response_retained=False,
      first_queries=['symplectic ball packing higher dimensions Siegel Yao 2025 relative isotopy space embeddings balls','Abouzaid Alvarez Gavela Courte Kragh tube nearby Lagrangian 2025 2026','Bai Xu Arnold conjecture integral coefficients minimal Chern number 2026'],
      retained_rounds=[
       dict(response='web2-response.json',queries=['site.arxiv.org symplectic embeddings balls higher dimensional isotopy knotted ball ball','site.arxiv.org Siegel Yao 2312.13224','site.arxiv.org nearby Lagrangians tube torsion Alvarez Gavela Igusa Sullivan','site.arxiv.org ball packing prescribed symplectic balls complement strong packing stability']),
       dict(response='web3-response.json',queries=['"symplectic" "balls into a ball" "connected"','"symplectic" "ball" "unknotted" "higher"','"space" "symplectic embeddings" "balls" "higher dimensions"']),
       dict(response='web4-response.json',open='https://www.ams.org/journals/notices/202106/noti2238/noti2238.html',failure='URL is not accessible via this tool'),
       dict(response='web5-response.json',queries=['site.arxiv.org "symplectic embedding problems" Schlenk 2017 survey','site.ams.org "Emb" "connected" "ball" "higher" "Schlenk"','"ball" "ball" "unknotted" "symplectic" McDuff'])],
      limitations='Bounded web discovery. Nonprimary hits are leads only. No exhaustion, priority, MathDB scoring, or global open-problem status inferred. Full first response not saved; no proof depends on it.'))
    print(json.dumps(dict(passages=len(passages),versions=len(versions),diagnostics=diag['total_assertions'])))
if __name__=='__main__':main()
