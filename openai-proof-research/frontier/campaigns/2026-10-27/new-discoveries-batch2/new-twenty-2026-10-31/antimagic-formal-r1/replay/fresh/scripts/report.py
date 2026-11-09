import hashlib,json,pathlib
root=pathlib.Path.cwd()
rows=[r.split('\t') for r in (root/'audit.tsv').read_text().splitlines()]
def summary(rs):
    return dict(total=len(rs),unsafe=sum(r[3]=='true' for r in rs),partial=sum(r[4]=='true' for r in rs),
        implemented_by=sum(r[5]=='true' for r in rs),extern=sum(r[6]=='true' for r in rs),
        unsafe_rec=sum('_unsafe_rec' in r[0] for r in rs),axioms=[r[0] for r in rs if r[2]=='axiom'])
local=[r for r in rows if r[1].startswith('Antimagic')]
upstream=[r for r in rows if not r[1].startswith('Antimagic')]
assert set(summary(rows)['axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(not summary(local)[k] for k in ['unsafe','partial','implemented_by','extern','unsafe_rec'])
result=dict(mathdb_id=354228,status='PARTIAL, NOT ACCEPTED',credit=0,
    endpoints={'Antimagic.even_case':'conditional on LowerBound and Construction',
      'Antimagic.mathdb_354228':'conditional on LowerBound, Construction, ModelBridge, ModelLeaves'},
    remaining_props=['ModelStructure','ModelBridge','ModelLeaves','LowerBound','Construction'],
    regression={'kernel_row_checks':[[t,n] for t in [2,4] for n in [1,2,3]],
      'literal_graph_regressions':'NOT COMPLETED; incidence bridge missing','python_cases':42},
    audit={'closure_equals_audited_set':True,'allowOpaque':True,'local':summary(local),'upstream':summary(upstream)},
    module_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.glob('*.lean'))},
    toolchain='Lean 4.34.1',mathlib_commit='d13f23b723b8a846827a245b89c10fc7d3f11612')
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['audit'],indent=2))
