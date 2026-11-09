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
assert len({r[0] for r in rows}) == len(rows)
for line in (root/'inherited-before.sha256').read_text().splitlines():
    digest,name=line.split()
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
result=dict(mathdb_id=354228,round='4A',status='PARTIAL, NOT ACCEPTED',credit=0,
    frozen_packet_sha256='9dc97086dd29e29d7d84932df93256c01c4531b9813e0be7f16af8410d589e6c',
    endpoints={'Antimagic.Round4A.even_case':'conditional on NonbinaryHigherConstruction and BinaryHigherConstruction',
      'Antimagic.Round4A.mathdb_354228':'conditional on NonbinaryHigherConstruction, BinaryHigherConstruction and ModelBridge'},
    discharged_props=['ModelStructure','ModelLeaves','LowerBound','Antimagic.Round3.DepthTwoConstruction'],
    closed_construction_cases=['n = 1, every t >= 2','n = 2, t = 2 (source Figure 5)','n = 2, every even t >= 4'],
    remaining_props=['Antimagic.Round3.NonbinaryHigherConstruction','Antimagic.Round3.BinaryHigherConstruction','Antimagic.ModelBridge'],
    remaining_construction_cases=['n >= 3, even t >= 2 including binary patch'],
    audit={'closure_equals_audited_set':True,'allowOpaque':True,'local':summary(local),'upstream':summary(upstream)},
    regression={'row_checks':[[t,n] for t in [2,4] for n in [1,2,3]],'python_cases':42,
      'literal_graph_construction':'general stars and binary depth two; literal finite certificates at all six regression parameters'},
    inherited_byte_identical=True,
    validation={'strict_serial_rebuild':True,'leanchecker_all_27_modules':True,'negative_controls':'inherited regression module and Python checker'},
    module_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.glob('*.lean'))},
    toolchain='Lean 4.34.1',mathlib_commit='d13f23b723b8a846827a245b89c10fc7d3f11612')
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['audit'],indent=2))
