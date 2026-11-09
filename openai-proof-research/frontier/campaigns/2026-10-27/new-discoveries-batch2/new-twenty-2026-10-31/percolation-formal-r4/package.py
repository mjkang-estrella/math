from pathlib import Path
import hashlib,json,re,zipfile
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');P=R/'packet';S=P/'src'
orig=(P/'module-order.txt').read_text().splitlines()[:92]
assert len(orig)==92
order=orig+['Collineation']+(R/'family-order.txt').read_text().splitlines()+['Noncollinear','Normalize','NormalizedExport','NormalizedLink']+(R/'normalized-order.txt').read_text().splitlines()+['AuditR4']
assert len(order)==len(set(order))
text='''import AuditR3
import NormalizedEndpoint
import NormalizedExport
import Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let localModules : Array String := #'''+json.dumps(order,separators=(',',':'))+'''
  for (n, ci) in env.constants.toList do
    let owner := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i]!.toString
      | none => "AuditR4"
    if localModules.contains owner then
      count := count + 1
      if ci.isUnsafe || ci.isPartial || (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n ||
          (n.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "Forbidden local declaration metadata: {n}"
      match ci with
      | .axiomInfo _ => throwError "Local assumption declaration: {n}"
      | _ => pure ()
  logInfo m!"Local declaration metadata audit passed: {count} declarations"
'''
(S/'AuditR4.lean').write_text(text)
assert set(order)=={p.stem for p in S.glob('*.lean')},(len(order),len(list(S.glob('*.lean'))))
(P/'module-order.txt').write_text('\n'.join(order)+'\n')
old=[]
with zipfile.ZipFile(R/'inherited-source.zip') as z:
 for n in z.namelist():
  if n.startswith('src/') and n.endswith('.lean'):
   a=z.read(n);b=(P/n).read_bytes();assert a==b;old.append({'path':n,'sha256':hashlib.sha256(b).hexdigest()})
assert len(old)==92
(R/'inherited-source-comparison.json').write_text(json.dumps(old,indent=2))
data=json.loads((R/'normalized-trimmed.json').read_text())['steps'];N=json.loads((R/'normalized-progress.json').read_text())['generated_steps']
(P/'replay-frontiers.tsv').write_text(''.join(f'NReplay{j//500:03d}\t{min(j+500,N)}\t{data[min(j+500,N)-1][0]}\t{data[min(j+500,N)][0] if min(j+500,N)<len(data) else 0}\n' for j in range(0,N,500)))
(P/'source-manifest.sha256').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(P))+'\n' for p in sorted(S.glob('*.lean'))))
for n in ['normalized-trimmed.json','normalized.cnf','certificate-sha256.json','generator-correspondence.json','generate_replay.py']:(P/n).write_bytes((R/n).read_bytes())
# Frozen source packet only; no build outputs or logs.
with zipfile.ZipFile(R/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(S.glob('*.lean')):z.write(p,str(p.relative_to(P)))
 for n in ['module-order.txt','source-manifest.sha256','guard.sh','replay.sh','scan.py','replay-frontiers.tsv','normalized-trimmed.json','normalized.cnf','certificate-sha256.json','generator-correspondence.json','generate_replay.py']:z.write(P/n,n)
with zipfile.ZipFile(R/'source-only.zip') as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
 z.extractall(R/'fresh-extracted')
print({'module_count':len(order),'archive_sha256':hashlib.sha256((R/'source-only.zip').read_bytes()).hexdigest()})
