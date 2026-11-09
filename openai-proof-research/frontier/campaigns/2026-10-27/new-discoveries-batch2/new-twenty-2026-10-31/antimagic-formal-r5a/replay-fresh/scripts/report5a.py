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
assert len({r[0] for r in rows})==len(rows)
manifest=(root/'inherited-before.sha256').read_text().splitlines()
assert len(manifest)==27
for line in manifest:
    digest,name=line.split()
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
result=dict(mathdb_id=354228,round='5A',status='PARTIAL, NOT ACCEPTED',credit=0,
 frozen_packet_sha256='2ecbbae0f5804c5d9c5d3a2b83b2789a7c359edc7162f2c3dbfc42f58cef8516',
 endpoints={'Antimagic.Round5A.even_case':['NonbinaryWeightCompletion','BinaryHigherConstruction'],
 'Antimagic.Round5A.mathdb_354228':['NonbinaryWeightCompletion','BinaryHigherConstruction','ModelBridge']},
 completed=['shell row interval disjointness and coverage','internal label permutation on actual nonroot internal vertices',
 'parent-derived tuple parameter permutation','leaf-row label permutation','global positive label range',
 'literal nonbinary higherLabeling edge equivalence and exact formula agreement',
 'nonbinary middle children sums','nonbinary constant leaf-parent incoming-plus-children sum'],
 remaining_props=['Antimagic.Round5A.NonbinaryWeightCompletion','Antimagic.Round3.BinaryHigherConstruction','Antimagic.ModelBridge'],
 remaining_work=['nonbinary literal weights via weight_row, global colour ranges, root separation, properness and exact colour count',
 'binary higher-depth construction (not started, target order preserved)','ModelBridge reserved for sibling lane'],
 audit={'closure_equals_audited_set':True,'allowOpaque':True,'local':summary(local),'upstream':summary(upstream)},
 regression={'requested_cases':[[t,n] for t in [2,4,6] for n in [3,4,5]],'negative_controls':['missing binary patch','duplicate label'],
 'inherited_regression':True},inherited_byte_identical=True,
 validation={'strict_serial_rebuild':True,'explicit_leanchecker_all_modules':True,'module_count':len(list(root.glob('*.lean')))},
 module_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.glob('*.lean'))},
 toolchain='Lean 4.34.1',mathlib_commit='d13f23b723b8a846827a245b89c10fc7d3f11612')
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['audit'],indent=2))
