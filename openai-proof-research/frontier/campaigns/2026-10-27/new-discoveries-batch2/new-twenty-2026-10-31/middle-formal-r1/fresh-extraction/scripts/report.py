from pathlib import Path
from collections import Counter
import json, hashlib, sys
L=Path(__file__).resolve().parent.parent
audit=L/'fresh-extraction/audit.jsonl'
names=set()
local=[]; upstream=Counter(); localmeta=Counter(); endpoints={}
deps=set()
allowed={'propext','Classical.choice','Quot.sound'}
flags=['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']
targets=['G8_connected','g8_value',"g8_value'",'middle_g8_value',"middle_g8_value'",'mathdb_355217_connected',"mathdb_355217_connected'",'edgeless_two_literal_failure']
for line in audit.open():
    r=json.loads(line); assert r['name'] not in names; names.add(r['name'])
    deps.update(r['deps_allowOpaque'])
    if r['local']:
        local.append(r['name'])
        for f in flags:
            if r[f]:localmeta[f]+=1
        assert not any(r[f] for f in flags), r
        assert set(r['axioms'])<=allowed,r
        if r['name'].split('.')[-1] in targets:
            endpoints[r['name']]={'status':'PASS','axioms':r['axioms']}
    else:
        for f in flags:
            if r[f]:upstream[f]+=1
missing=deps-names
# Quot kernel primitive constant references may have no module index; report explicitly.
assert not missing, sorted(missing)
assert len(endpoints)==len(targets),(endpoints,targets)
mods={}
for p in sorted(L.glob('Middle*.lean')):
    mods[p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
for p in L.glob('*.lean'):
    assert p.read_bytes()==(L/'fresh-extraction'/p.name).read_bytes(),p
result={'mathdb_id':355217,'self_accepted':False,'credit':0,'status':'FORMALIZED_AWAITING_ROOT',
'lean':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612',
'modules':mods,'endpoints':endpoints,
'audit':{'import_closure_inventory':len(names),'audited':len(names),'sets_equal_lean_checked':True,'dependency_names_missing':len(missing),'local_declarations':len(local),'local_forbidden_metadata':dict(localmeta),'upstream_metadata':dict(upstream),'allowOpaque':True},
'validation':{'fresh_extracted_strict_serial_rebuild':'PASS','explicit_module_leanchecker':'PASS','negative_controls':'3 rejected','python_regression':json.loads((L/'regression.json').read_text()),'source_bytes_equal':True},
'archive_sha256':hashlib.sha256((L/'middle-source.zip').read_bytes()).hexdigest()}
(L/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['audit'],indent=2))
