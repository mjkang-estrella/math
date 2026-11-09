import hashlib,json,pathlib
root=pathlib.Path.cwd()
rows=[r.split('\t') for r in (root/'audit.tsv').read_text().splitlines()]
def summary(rs):
 return dict(total=len(rs),unsafe=sum(r[3]=='true' for r in rs),partial=sum(r[4]=='true' for r in rs),implemented_by=sum(r[5]=='true' for r in rs),extern=sum(r[6]=='true' for r in rs),unsafe_rec=sum('_unsafe_rec' in r[0] for r in rs),axioms=[r[0] for r in rs if r[2]=='axiom'])
local=[r for r in rows if r[1].startswith('Antimagic')]
upstream=[r for r in rows if not r[1].startswith('Antimagic')]
assert set(summary(rows)['axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(not summary(local)[k] for k in ['unsafe','partial','implemented_by','extern','unsafe_rec'])
assert len({r[0] for r in rows})==len(rows)
manifest=(root/'inherited-before.sha256').read_text().splitlines()
assert len(manifest)==37
for line in manifest:
 digest,name=line.split()
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
modules=sorted(root.glob('*.lean'))
assert len(modules)==45
assert all((root/'build'/f'{p.stem}.checked').exists() for p in modules)
result=dict(mathdb_id=354228,round='6A',status='PARTIAL, NOT ACCEPTED',credit=0,
 frozen_packet_sha256='98da5a1eccd29872f87e21aba876478405dacf325818f7b9042b3a1ccea02aef',
 endpoints={'Antimagic.Round6A.even_case':['Antimagic.Round3.BinaryHigherConstruction'],
 'Antimagic.Round6A.mathdb_354228':['Antimagic.Round3.BinaryHigherConstruction','Antimagic.ModelBridge']},
 closed_props=['Antimagic.Round5A.NonbinaryWeightCompletion','Antimagic.Round3.NonbinaryHigherConstruction'],
 remaining_props=['Antimagic.Round3.BinaryHigherConstruction','Antimagic.ModelBridge'],
 completed=['nonbinary global weight bands','nonbinary root formula and separation','nonbinary properness and exactly t^n+1 colours','binary patch row permutation','binary internal label injectivity and coverage','binary explicit row-two labels','binary literal root and first-row weights conditional on formula realization','binary root separation'],
 remaining_work=['binary parent-derived leaf parameter permutation, leaf bijection and literal labeling','binary remaining weights, properness and exact colour count','ModelBridge integration only after both construction targets close'],
 audit={'closure_equals_audited_set':True,'allowOpaque':True,'local':summary(local),'upstream':summary(upstream)},
 regression={'requested_cases':[[t,n] for t in [2,4,6] for n in [3,4,5]],'negative_controls':['missing binary patch','duplicate label','l colours','odd t'],'inherited_regression':True},
 inherited_byte_identical=True,validation={'strict_serial_rebuild':True,'explicit_leanchecker_all_modules':True,'module_count':len(modules)},
 module_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in modules},
 toolchain='Lean 4.34.1',mathlib_commit='d13f23b723b8a846827a245b89c10fc7d3f11612')
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['audit'],indent=2))
