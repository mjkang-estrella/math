"""Fresh strict replay of the graded spectral bridge, not the source conjecture."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess
B=Path(__file__).resolve().parents[1]
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
L=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
fresh=B/'verification'/'fresh'
if fresh.exists(): shutil.rmtree(fresh)
fresh.mkdir(parents=True)
modules=['ScalarCore','SpectralCore','PolarFrameBridge','HSBridge','ContractiveBridge','GradedSpectralBridge','GradingConsequences','ProjectionFrames','RangeFrames']
names=[]
for mod in modules:
    p=B/'formal'/f'{mod}.lean';s=p.read_text()
    if re.search(r'\b(sorry|admit|unsafe|native_decide)\b|^\s*axiom\b',s,re.M):
        raise RuntimeError('forbidden proof token')
    names += ['FourProjection.'+v for v in re.findall(r'^\s*(?:@\[[^\n]+\]\s*)?(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([\w.]+)',s,re.M)]
    (fresh/p.name).write_bytes(p.read_bytes())
checks='import GradingConsequences\nimport RangeFrames\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n'
(fresh/'Checks.lean').write_text(checks)
(B/'formal'/'Checks.lean').write_text(checks)
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(fresh)]+[str(x/'.lake/build/lib/lean') for x in sorted(P.iterdir()) if (x/'.lake/build/lib/lean').is_dir()]))
for mod in modules+['Checks']:
    p=subprocess.run([str(L),'-DwarningAsError=true','-o',str(fresh/f'{mod}.olean'),str(fresh/f'{mod}.lean')],cwd=fresh,env=env,text=True,capture_output=True)
    log=p.stdout+p.stderr
    (fresh/f'{mod}.log').write_text(log)
    print(mod,p.returncode,flush=True)
    if p.returncode:
        print(log);raise SystemExit(p.returncode)
log=(fresh/'Checks.log').read_text()
reports=dict(re.findall(r"'([\w.]+)' depends on axioms: \[(.*?)\]",log,re.S))
for n in re.findall(r"'([\w.]+)' does not depend on any axioms",log): reports[n]=''
if set(reports)!=set(names): raise RuntimeError(('axiom inventory mismatch',names,reports))
axioms=sorted({a.strip() for r in reports.values() for a in r.split(',') if a.strip()})
if set(axioms)-{'propext','Classical.choice','Quot.sound'}:raise RuntimeError('unexpected axiom')
manifest=json.loads((P.parent.parent/'lake-manifest.json').read_text())
mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
assert mathlib['rev']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
result={
 'status':'PASS_INTEGRATED_SUPPORT_COMPONENTS',
 'source_conjecture_formalized':False,
 'compiler':subprocess.check_output([str(L),'--version'],text=True).strip(),
 'compiler_path':str(L),'compiler_sha256':hashlib.sha256(L.read_bytes()).hexdigest(),
 'mathlib_revision_from_manifest':mathlib['rev'],
 'warningAsError':True,'fresh_local_olean_build':True,
 'public_declaration_count':len(names),'declarations':names,'axioms':axioms,
 'declaration_axioms':{n:[a.strip() for a in r.split(',') if a.strip()] for n,r in reports.items()},
 'sources':[{'path':str((B/'formal'/f'{m}.lean').relative_to(B)),'sha256':hashlib.sha256((B/'formal'/f'{m}.lean').read_bytes()).hexdigest()} for m in modules],
 'scope':'Two independent Hermitian spectral bases; CFC square-root grading and entry relation; actual spectrum bounds from positive shifts; unitary-invariant Gram contractivity; contraction of cross-Gram isometries; HS/trace spectral inequality. Empty types permitted. Not the source four-projection endpoint.',
}
(B/'verification'/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','public_declaration_count','axioms']},indent=2))
