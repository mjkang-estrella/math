"""One-time development operation, never imported or run by verify.py.
Supply the validated_inventory_sha256 returned by the completed --preseal replay.
Fails on any changed owned byte, any noncanonical path, or an existing seal.
"""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i128_statistical_learning_discovery'
E='frontier/experiments/i128_statistical_learning_discovery'
REPORT='frontier/iterations/i128-statistical-learning-discovery.md'
def main(digest):
    seal=ROOT/S/'seal.json'
    assert not seal.exists(),'a final seal already exists; never repair/reseal'
    ps=[REPORT]
    for base in [S,E]:
        for p in (ROOT/base).rglob('*'):
            assert not p.is_symlink()
            if p.is_file():ps.append(str(p.relative_to(ROOT)))
    assert len(ps)==len(set(ps))
    ps=sorted(ps)  # GLOBAL order, not concatenated directory traversal order.
    assert ps==sorted(set(ps))
    rows=[]
    for p in ps:
        b=(ROOT/p).read_bytes();rows.append({'path':p,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    actual=hashlib.sha256(json.dumps(rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    assert actual==digest,'owned evidence changed since the completed preseal replay'
    data={'schema':'i128-exact-owned-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','roots':[REPORT,S+'/',E+'/'],'validated_inventory_sha256':actual,'files':rows}
    assert [d['path'] for d in data['files']]==sorted(set(d['path'] for d in data['files']))
    with seal.open('x') as f:f.write(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'files_excluding_seal':len(rows),'artifacts_including_seal':len(rows)+1,'seal_sha256':hashlib.sha256(seal.read_bytes()).hexdigest(),'global_path_order':'PASS','one_final_seal_created':True}))
if __name__=='__main__':
    assert len(sys.argv)==2
    main(sys.argv[1])
