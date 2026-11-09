# The source is maintained in formal/Eventown.lean. Validate its explicit permutation certificates.
import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'outputs/groups-S-5-None.json').read_text())['witness']
assert len(x)==8 and len(set(map(tuple,x)))==8
for p in x: assert sorted(p)==list(range(5))
print('Eight explicit bijections validated; Lean source is formal/Eventown.lean.')
