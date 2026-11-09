from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).resolve().parent
base=p.parents[1]; old=base/'lanes/sol-mathdb-primary-qualified-breadth-r482'
# Bind actual inputs, without copying the historical evidence tree.
bindings=json.loads((p/'input-bindings.json').read_text()); checks=[]
root=Path('/home/mj-kang/Documents/Dev/math')
for name,expected in bindings.items():
 f=root/name; actual=hashlib.sha256(f.read_bytes()).hexdigest();checks.append(dict(path=str(f),expected=expected,actual=actual,matches=actual==expected))
(p/'input-validation.json').write_text(json.dumps(checks,indent=2)+'\n')
prov=json.loads((old/'source-provenance.json').read_text())
rows=[x for x in prov if '1809.01769' in str(x)]
for suf in ['pdf','txt']:
 f=old/f'sources/1809.01769.{suf}'; rows.append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size,inspected_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='v1 sections 2.1–2.4, Theorem2 reflection proof, Theorem3 continuity proof, Lemma5 proof'))
(p/'historical-source-receipts.json').write_text(json.dumps(rows,indent=2)+'\n')
r=dict(mathdb_id=340297,status='PARKED_UNPROVED_EXACT_ONE_SIDED_PROGRESS',accepted_credit=0,source='Bian arXiv:1809.01769v1 Conjecture3',literal_quantifier='Every global minimizing distinct-anchor configuration satisfying a self-inverse permutation is reflection symmetric.',exact_asymmetric_endpoint_calculation=json.loads((p/'exact-endpoint.json').read_text()),ordinary_geometric_completeness_argument='SUMMARY.md',symmetric_global_bound=False,minimizer_existence=False,source_degeneracies_fully_resolved=False,lean_endpoint=None,kernel_checked=False,axiom_audit=None,clean_extracted_lean_replay=None,novelty='Not cleared; bounded live primary and registry screening only.',branch_discovery=json.loads((p/'symmetric-branch-extended.json').read_text()),precise_obstructions=['No global symmetric lower bound at 6471/10000, including all boundary and tie cases.', 'No proof that the infimum in the source distinct-anchor permutation class is attained.', 'No kernel-checked endpoint enumeration or geometric/source bridges.'],resource_use='At most two task CPU processes, BLAS threads limited to one; 500000-node discovery cap; symbolic solve stopped after about 30 seconds. No agents/git/browser/public posting/shared edits.')
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
