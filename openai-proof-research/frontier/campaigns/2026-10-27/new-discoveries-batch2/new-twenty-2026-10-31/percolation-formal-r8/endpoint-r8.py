from pathlib import Path
import json,shutil
r=Path(__file__).resolve().parent;s=r/'packet/src';f=r/'optimized-extracted'
order=(f/'module-order.txt').read_text().splitlines();order=[m for m in order if (f/f'logs/{m}.ok').exists() and m not in ['EndpointR8','AuditR8']]
g=json.loads((r/'generation.json').read_text());last=next(m for m in reversed(order) if m.startswith('R8Chain'));end=g[last]['end'];d=json.loads((r/'normalized-trimmed.json').read_text());idx,c,hs=d['steps'][end-1]
a=b=0
for x in c:
 if x>0:a|=1<<(x-1)
 else:b|=1<<(-x-1)
if end==len(d['steps']):
 assert not c
 text=f'''import {last}
namespace Percolation
set_option autoImplicit false
abbrev NormalizedCNFUnsat5 := GeneratedNormalizedUnsat5
theorem normalizedCNFUnsat5 : NormalizedCNFUnsat5 := by
  rintro ⟨v, hv⟩
  obtain ⟨n, b, hn, _⟩ := MaskChain.clause{idx} v hv
  cases b <;> simp [MaskRUP.bits, MaskChain.maskR8_{idx}] at hn
theorem noMinimalTwoRound5_unconditional : NoMinimalTwoRound5 :=
  normalized_unsat_implies_noMinimal5 normalizedCNFUnsat5
theorem not_conjecture20_unconditional : ¬ Conjecture20 :=
  not_conjecture20_normalized normalizedCNFUnsat5
#print axioms normalizedCNFUnsat5
#print axioms noMinimalTwoRound5_unconditional
#print axioms not_conjecture20_unconditional
#print not_conjecture20_unconditional
end Percolation
'''
 endpoint='Percolation.not_conjecture20_unconditional';statement='¬ Percolation.Conjecture20'
else:
 text=f'''import {last}
namespace Percolation.MaskChain
set_option autoImplicit false
-- Precisely the semantic obligation for zero-based additions [{end},129671).
def RemainingSuffixUnsatR8 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    MaskRUP.Holds (v ∘ decodeVar) ({a}, {b})
end Percolation.MaskChain
namespace Percolation
set_option autoImplicit false
theorem not_conjecture20_mask_after{end}
    (h : MaskChain.RemainingSuffixUnsatR8) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,MaskChain.clause{idx} v hv⟩
#print axioms not_conjecture20_mask_after{end}
#print not_conjecture20_mask_after{end}
end Percolation
'''
 endpoint=f'Percolation.not_conjecture20_mask_after{end}';statement='Percolation.MaskChain.RemainingSuffixUnsatR8 → ¬ Percolation.Conjecture20'
(s/'EndpointR8.lean').write_text(text);order+=['EndpointR8'];allmods=order+['AuditR8']
audit='\n'.join('import '+m for m in order)+'''\nimport Lean
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array String := #'''+json.dumps(allmods,separators=(',',':'))+'''
  for m in modules do
    if m != "AuditR8" && !(env.header.moduleNames.any (fun n => n.toString == m)) then
      throwError "Missing module {m}"
  let mut owners : Std.HashSet String := {}
  for m in modules do owners := owners.insert m
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i]!.toString
      | none => "AuditR8"
    if owners.contains owner then
      count := count + 1
      if info.isUnsafe || info.isPartial || (Lean.Compiler.getImplementedBy? env name).isSome || Lean.isExtern env name || (name.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "Rejected declaration metadata: {name}"
      match info with
      | .axiomInfo _ => throwError "Local assumption {name}"
      | _ => pure ()
  logInfo m!"Metadata audit passed: {count} declarations"
'''
(s/'AuditR8.lean').write_text(audit)
for m in ['EndpointR8','AuditR8']:shutil.copyfile(s/f'{m}.lean',f/'src'/f'{m}.lean')
for p in [r/'packet/module-order.txt',f/'module-order.txt',r/'module-order.txt']:p.write_text('\n'.join(allmods)+'\n')
(r/'endpoint.json').write_text(json.dumps({'endpoint':endpoint,'statement':statement,'closed_additions':end,'last_id':idx,'last_mask':[a,b]},indent=2))
print(endpoint,statement)
