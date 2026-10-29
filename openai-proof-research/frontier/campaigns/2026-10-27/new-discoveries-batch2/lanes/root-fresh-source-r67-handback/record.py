import hashlib,json,shutil,subprocess,sys
from fractions import Fraction as F
from pathlib import Path
from datetime import datetime,timezone
batch=Path(__file__).resolve().parent.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n in (67,69):
    here=batch/f'lanes/root-fresh-source-r{n}-handback';here.mkdir(exist_ok=True)
    lane=batch/f'lanes/sol-fresh-source-discovery-r{n}'
    if n==67:
        prov=json.loads((lane/'provenance.json').read_text())
        manifest={r['path']:r['sha256'] for r in prov['artifacts']}
    else:
        manifest=json.loads((lane/'SHA256SUMS.json').read_text())
    rows=[{'path':k,'expected':v,'actual':sha(lane/k)} for k,v in manifest.items()]
    bad=[r for r in rows if r['actual']!=r['expected']]
    assert all('finalize' in r['path'] and r['path'].endswith(('.log','.json')) for r in bad),bad
    if n==67:
        x=F(1,10);p=[F(1)];dp=[F(0)]
        sigma=lambda k:sum(d*d for d in range(1,k+1) if k%d==0)
        for k in range(1,14):
            a=sum(sigma(j)*p[k-j] for j in range(1,k+1))
            b=sum(sigma(j)*dp[k-j] for j in range(1,k+1))
            p.append(x*a/k);dp.append((a+x*b)/k)
        w=13*dp[12]*p[13]-12*p[12]*dp[13]
        assert w<0
        assert F(3)*6*F(11,2)-F(2)*F(11,2)*F(65,6)==F(-121,6)
        checks={'D12_at_one_tenth':str(w),'scope':'Below source x threshold; method obstruction only','generic_W2':str(F(-121,6))}
        target='Heim-Neuhauser published Conjecture1, both specified n/x ranges'
        gap='All-index suffix domination or a direct uniform source inequality; finite derivative and coefficient checks are not proof.'
        replay='Independent exact scalar recurrence and its derivative give D12(1/10)<0; generic positive-input W2(1)=-121/6 checked. Full worker suites not rerun.'
    else:
        copy=here/'check-copy';copy.mkdir(exist_ok=True)
        shutil.copyfile(lane/'exact.py',copy/'exact.py')
        with (here/'exact.log').open('w') as log:
            subprocess.run([sys.executable,'-B','exact.py'],cwd=copy,stdout=log,stderr=subprocess.STDOUT,check=True)
        assert (copy/'exact.json').read_bytes()==(lane/'exact.json').read_bytes()
        checks=json.loads((copy/'exact.json').read_text())
        target='MO476529: convolution closure of positive even squared-radius log-convex densities'
        gap='Uniform two-input score-variance/mean-curvature inequality plus nonsmooth approximation; expert identity attribution remains independently HOLD.'
        replay='Exact symbolic score, heat and chain-rule identities plus64 rational Gaussian cancellations replayed in own copy; JSON byte-identical. Floating diagnostic suites not rerun.'
    (here/'root-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
    receipt={'utc':datetime.now(timezone.utc).isoformat(),'status':'UNRESOLVED handback preserved','credit':0,'counts':[7,37],
      'target':target,'gap':gap,'root_validation':replay,'input_hashes':rows,'hash_mismatches':bad,
      'limits':['No full source proof or counterexample.','Registry freshness HOLD retained.','No root full source/novelty review or Lean PASS.','No acceptance, paper or count change.']}
    (here/'ADOPTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    assert all(sha(lane/r['path'])==r['actual'] for r in rows)
    paths=[str(p.relative_to(Path.cwd())) for root in (lane,here) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='pathspec.txt']
    if n==69:
        nxt=batch/'NEXT.md';s=nxt.read_text()
        s=s.replace('Three fresh Sol high/default research lanes r70 finite structures, r69 analysis,\nr67 arithmetic/algebra are active; no children.', 'r67 Heim-Neuhauser and r69 squared-radius convolution closure remain unresolved.\nRoot exact diagnostic replays are preserved; r69 expert-authorship HOLD is\nseparate from its missing uniform inequality. No credit added.\nThree fresh Sol high/default research lanes r70 finite structures, r72 analysis,\nr71 arithmetic/algebra are active; no children.')
        nxt.write_text(s);paths.append(str(nxt.relative_to(Path.cwd())))
    (here/'pathspec.txt').write_text('\n'.join(paths)+'\n')
    print(json.dumps({'lane':n,'hashes':len(rows),'mismatches':bad,'root_check':'PASS','credit':0}))
