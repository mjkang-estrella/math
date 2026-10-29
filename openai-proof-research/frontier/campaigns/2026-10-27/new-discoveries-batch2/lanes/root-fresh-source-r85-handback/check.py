import hashlib, json
from pathlib import Path
from datetime import datetime, timezone

root = Path(__file__).resolve().parent
lane = root.parent / 'sol-fresh-source-discovery-r85'
def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''): h.update(block)
    return h.hexdigest()
manifest = json.loads((lane/'provenance.json').read_text())['files_sha256']
actual = {p: sha(lane/p) for p in manifest}
drift = {p: {'expected': manifest[p], 'actual': actual[p]} for p in manifest if manifest[p] != actual[p]}
assert not drift, drift
# Independent exact check of the generic same-spectrum obstruction only.
A = ((1,0),(0,3)); B = ((2,1),(1,2))
det = lambda M: M[0][0]*M[1][1]-M[0][1]*M[1][0]
assert sum(A[i][i] for i in range(2)) == sum(B[i][i] for i in range(2)) == 4
assert det(A) == det(B) == 3
nullities=[]
for M in (A,B):
    kernel=[(x,y) for x in range(2) for y in range(2)
            if ((M[0][0]-1)*x+M[0][1]*y)%2 == 0
            and (M[1][0]*x+(M[1][1]-1)*y)%2 == 0]
    nullities.append({1:0,2:1,4:2}[len(kernel)])
assert nullities == [2,1]
assert det(((1,2),(0,1))) == 1  # [e1, B e1]
record = {'utc':datetime.now(timezone.utc).isoformat(), 'status':'UNRESOLVED', 'credit':0,
 'counts':{'additional':8,'total':38}, 'manifest_verified':len(manifest), 'drift':drift,
 'provenance_sha256':sha(lane/'provenance.json'), 'root_check':'same-spectrum integral-cyclicity obstruction; nullities [2,1] modulo 2',
 'gap':'Universal integral primitive cyclic gluing is unproved; finite-field tests are only necessary conditions.',
 'limits':'Root read SUMMARY and discovery; did not repeat 5145 worker checks or independently clear full prior art. Generic matrices are not claimed differential-poset operators. No full proof or formal certificate.',
 'preserved_manifest':actual}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'pass':True,'hashes':len(manifest),'credit':0}))
