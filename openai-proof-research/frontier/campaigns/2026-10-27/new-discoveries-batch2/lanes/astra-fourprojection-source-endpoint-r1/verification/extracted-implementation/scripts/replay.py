"""Fresh isolated strict replay; inspect actual environment, including private and generated names."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess
B=Path(__file__).resolve().parents[1]
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
L=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
modules=['ScalarCore','SpectralCore','PolarFrameBridge','HSBridge','ContractiveBridge','GradedSpectralBridge','GradingConsequences','BoundaryChecks','FrameReconstruction','FrameBlocks','FrameInequality','FrameBoundaryChecks','ProjectionFrames','RangeFrames','SourceEndpoint','SourceBoundaryChecks']
fresh=B/'verification/fresh'
if fresh.exists():shutil.rmtree(fresh)
fresh.mkdir(parents=True)
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(fresh)]+[str(x/'.lake/build/lib/lean') for x in sorted(P.iterdir()) if (x/'.lake/build/lib/lean').is_dir()]))
commands=[]
def compile(mod):
 cmd=[str(L),'-DwarningAsError=true','-o',str(fresh/f'{mod}.olean'),str(fresh/f'{mod}.lean')]
 p=subprocess.run(cmd,cwd=fresh,env=env,text=True,capture_output=True)
 (fresh/f'{mod}.log').write_text(p.stdout+p.stderr)
 commands.append({'command':cmd,'returncode':p.returncode})
 print(mod,p.returncode,flush=True)
 if p.returncode:
  print((p.stdout+p.stderr)[:6000]);raise SystemExit(p.returncode)
for mod in modules:
 f=B/'formal'/f'{mod}.lean';s=f.read_text()
 if re.search(r'\b(sorry|admit|unsafe|native_decide)\b|^\s*axiom\b',s,re.M):raise RuntimeError('forbidden proof token: '+mod)
 (fresh/f.name).write_bytes(f.read_bytes());compile(mod)
imports='import SourceBoundaryChecks\nimport FrameBoundaryChecks\n'
selected=', '.join('"'+m+'"' for m in modules)
audit=imports+'''open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let selected : List String := ['''+selected+''']
  let names := env.constants.toList.filterMap fun (n, _) =>
    match env.getModuleIdxFor? n with
    | some i => if selected.contains (env.header.moduleNames[i]!.toString) then some n else none
    | none => none
  for n in names.mergeSort (fun a b => a.toString ≤ b.toString) do
    logInfo m!"INVENTORY|{n}"
    elabCommand (← `(#check $(mkIdent n)))
    elabCommand (← `(#print axioms $(mkIdent n)))
'''
(fresh/'Inventory.lean').write_text(audit);compile('Inventory')
log=(fresh/'Inventory.log').read_text()
names=re.findall(r'^INVENTORY\|(.+)$',log,re.M)
source_names=[]
for mod in modules:
 source_names += ['FourProjection.'+v for v in re.findall(r'^\s*(?:@\[[^\n]+\]\s*)?(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|instance)\s+([\w.]+)',(B/'formal'/f'{mod}.lean').read_text(),re.M)]
assert set(source_names) <= set(names), set(source_names)-set(names)
reports=dict(re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",log,re.S))
for n in re.findall(r"'([^']+)' does not depend on any axioms",log):reports[n]=''
if set(names)!=set(reports):raise RuntimeError(('axiom inventory mismatch',set(names)-set(reports),set(reports)-set(names)))
axioms=sorted({a.strip() for r in reports.values() for a in r.split(',') if a.strip()})
if set(axioms)-{'propext','Classical.choice','Quot.sound'}:raise RuntimeError('unexpected axiom')
(fresh/'ExplicitInventory.lean').write_text(audit.replace('open Lean Elab Command in','set_option pp.all true\nset_option pp.proofs true\nset_option pp.maxSteps 100000000\nset_option pp.deepTerms true\nset_option format.width 120\nopen Lean Elab Command in'))
compile('ExplicitInventory')
endpoint=imports+'''set_option pp.maxSteps 100000000
set_option pp.deepTerms true
set_option pp.proofs true
set_option format.width 120
#print FourProjection.four_projection_inequality
#print axioms FourProjection.four_projection_inequality
#print FourProjection.banica_nechita_conjecture_6_6
#print axioms FourProjection.banica_nechita_conjecture_6_6
#print FourProjection.ProjectionFrameIndex
#print FourProjection.projectionFrameIndex_fintype
#print FourProjection.mpInvSqrt
#print Matrix.rank
'''
(fresh/'EndpointPrint.lean').write_text(endpoint);compile('EndpointPrint')
(fresh/'EndpointExplicitPrint.lean').write_text(endpoint.replace('set_option pp.proofs true','set_option pp.all true\nset_option pp.proofs true'))
compile('EndpointExplicitPrint')
for mod in ['ExplicitInventory','EndpointPrint','EndpointExplicitPrint']:
 if '⋯' in (fresh/f'{mod}.log').read_text(): raise RuntimeError('elided full print: '+mod)
manifest=json.loads((P.parent.parent/'lake-manifest.json').read_text());mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
assert mathlib['rev']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
result={'status':'PASS_LITERAL_SOURCE_ENDPOINT','source_conjecture_formalized':True,'acceptance_claim':False,'compiler':subprocess.check_output([str(L),'--version'],text=True).strip(),'compiler_path':str(L),'compiler_sha256':hashlib.sha256(L.read_bytes()).hexdigest(),'mathlib_revision_from_manifest':mathlib['rev'],'warningAsError':True,'fresh_local_olean_build':True,'module_count':len(modules),'public_source_declaration_count':len(source_names),'public_source_declarations':source_names,'actual_declaration_count':len(names),'declarations':names,'axioms':axioms,'declaration_axioms':{n:[a.strip() for a in r.split(',') if a.strip()] for n,r in reports.items()},'sources':[{'path':str((B/'formal'/f'{m}.lean').relative_to(B)),'sha256':hashlib.sha256((B/'formal'/f'{m}.lean').read_bytes()).hexdigest()} for m in modules],'commands':commands,'scope':'Arbitrary finite square complex Hermitian idempotents; literal CFC inverse square roots, ordinary linear-map range intersections. Stronger rank-free endpoint and source wrapper with both ordinary matrix rank balances. Empty dimensions allowed.'}
(B/'verification/result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','module_count','actual_declaration_count','axioms']},indent=2))
