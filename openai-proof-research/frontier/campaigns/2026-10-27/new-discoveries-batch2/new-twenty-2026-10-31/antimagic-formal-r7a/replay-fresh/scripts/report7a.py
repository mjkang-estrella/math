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
assert len(manifest)==45
for line in manifest:
 digest,name=line.split()
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
modules=sorted(root.glob('*.lean'))
assert all((root/'build'/f'{p.stem}.checked').exists() for p in modules)
result=dict(mathdb_id=354228,round='7A',status='IMPLEMENTED, NOT ACCEPTED',credit=0,
 frozen_packet_sha256='da0804d364b31a0359a8aef5592ef52249b097371e63f3848ede74bda6c64d88',
 bridge_packet_sha256='01116203a1ed83a81c90684ceb468113f0b4648104446fa3603dd24ce4c933ce',
 endpoints={'Antimagic.Round7A.even_case':[],'Antimagic.Round7A.mathdb_354228':[]},
 closed_props=['Antimagic.Round3.BinaryHigherConstruction'],remaining_props=[],
 audit={'closure_equals_audited_set':True,'allowOpaque':True,'local':summary(local),'upstream':summary(upstream)},
 inherited_byte_identical=True,validation={'strict_serial_rebuild':True,'explicit_leanchecker_all_modules':True,'module_count':len(modules)},
 module_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in modules},
 toolchain='Lean 4.34.1',mathlib_commit='d13f23b723b8a846827a245b89c10fc7d3f11612')
(root/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['audit'],indent=2))
assert len(modules)==54
assert summary(local)['total']==1434
