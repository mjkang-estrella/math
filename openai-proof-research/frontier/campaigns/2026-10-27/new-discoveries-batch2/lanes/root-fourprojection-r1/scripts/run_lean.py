"""Fresh strict replay of the PARTIAL spectral core, not of the source conjecture."""
from pathlib import Path
import os, subprocess, json, hashlib, re, shutil
B=Path(__file__).resolve().parents[1]
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
L='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
build=B/'verification'/'fresh'; build.parent.mkdir(exist_ok=True)
if build.exists(): shutil.rmtree(build)
build.mkdir()
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(build)]+[str(x/'.lake/build/lib/lean') for x in P.iterdir() if (x/'.lake/build/lib/lean').is_dir()]))
modules=['ScalarCore','SpectralCore']; names=[]; sources=[]
for mod in modules:
 src=B/'formal'/f'{mod}.lean'; txt=src.read_text()
 if re.search(r'\b(sorry|admit|unsafe|native_decide)\b|^\s*axiom\b',txt,re.M): raise RuntimeError('forbidden proof token')
 names += ['FourProjection.'+n for n in re.findall(r'^\s*(?:lemma|theorem)\s+(\w+)',txt,re.M)]
 (build/src.name).write_bytes(src.read_bytes())
 sources.append(dict(file=str(src.relative_to(B)),sha256=hashlib.sha256(src.read_bytes()).hexdigest()))
(build/'Checks.lean').write_text('\n'.join('import '+m for m in modules)+'\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n')
logs=[]
for mod in modules+['Checks']:
 p=subprocess.run([L,'-DwarningAsError=true','-o',str(build/f'{mod}.olean'),str(build/f'{mod}.lean')],cwd=build,env=env,text=True,capture_output=True)
 log=p.stdout+p.stderr;(build/f'{mod}.log').write_text(log);logs.append(log)
 print(mod,p.returncode,flush=True)
 if p.returncode: print(log);raise SystemExit(p.returncode)
reports=re.findall(r"'([\w.]+)' depends on axioms: \[(.*?)\]",logs[-1],re.S)
if sorted(n for n,a in reports)!=sorted(names):raise RuntimeError('axiom inventory mismatch')
axioms=sorted({x.strip() for n,a in reports for x in a.split(',')})
if set(axioms)-{'propext','Classical.choice','Quot.sound'}:raise RuntimeError('unexpected axiom')
result=dict(status='PASS_PARTIAL_CORE_ONLY',source_conjecture_formalized=False,compiler=subprocess.check_output([L,'--version'],text=True).strip(),mathlib_revision_required='d13f23b723b8a846827a245b89c10fc7d3f11612',declarations=names,axioms=axioms,sources=sources,scope='Scalar and finite spectral-array estimates. All literal source matrix/frame bridges remain pending.')
(B/'verification'/'result.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
