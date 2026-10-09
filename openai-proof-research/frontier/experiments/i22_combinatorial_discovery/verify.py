"""Offline provenance verifier; shared-input drift is reported separately."""
from pathlib import Path
import hashlib, json, sys

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i22_combinatorial_discovery'
REPORT='frontier/iterations/i22-combinatorial-discovery.md'
E=ROOT/'frontier/experiments/i22_combinatorial_discovery'
EXCLUDE={str((S/'artifact-seal.json').relative_to(ROOT)),str((S/'verification.json').relative_to(ROOT))}

def sha(data): return hashlib.sha256(data).hexdigest()
def records():
    paths={ROOT/REPORT}
    for base in (S,E):
        paths.update(p for p in base.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    return [{'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}
            for p in sorted(paths) if str(p.relative_to(ROOT)) not in EXCLUDE]

def main():
    if '--seal' in sys.argv:
        (S/'artifact-seal.json').write_text(json.dumps(records(),indent=2)+'\n')
    failures=[];drift=[];counts={}
    def check(ok,detail):
        if not ok:failures.append(detail)
    inputs=json.loads((S/'inputs.json').read_text())
    for r in inputs:
        frozen=ROOT/r['snapshot'];live=ROOT/r['path']
        check(frozen.is_file() and sha(frozen.read_bytes())==r['sha256'],'frozen input '+r['path'])
        if not live.is_file() or sha(live.read_bytes())!=r['sha256']:drift.append(r['path'])
    counts['frozen_inputs']=len(inputs)
    tree=json.loads((S/'inputs/sources/preprints-tree.json').read_text());blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
    manifest=json.loads((S/'pinned-manifest.json').read_text())
    pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    for r in manifest:
        p=S/'pinned'/r['path'];b=p.read_bytes()
        check(sha(b)==r['sha256'] and len(b)==r['bytes'],'source SHA256 '+r['path'])
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        check(blob==r['git_blob']==blobs[r['path']],'source Git blob '+r['path'])
        check(r['url']=='https://raw.githubusercontent.com/openai/math/'+pin+'/'+r['path'],'immutable URL '+r['path'])
    counts['pinned_sources']=len(manifest)
    for filename in ('source-contracts.json','read-locators.json','primary-contracts.json'):
        rows=json.loads((S/filename).read_text())
        for r in rows:
            t=(ROOT/r['path']).read_text()
            if 'start_char' in r:actual=t[r['start_char']:r['end_char']]
            else:actual=''.join(t.splitlines(keepends=True)[r['first_line']-1:r['last_line']])
            check(actual==r['text'] and sha(actual.encode())==r['sha256'],filename+' '+r['path'])
        counts[filename]=len(rows)
    literature=json.loads((S/'literature/manifest.json').read_text())
    for r in literature:
        p=ROOT/r['path'];check(p.is_file() and sha(p.read_bytes())==r['sha256'],'primary '+r['path'])
    counts['primary_artifacts']=len(literature)
    for r in json.loads((S/'external-dependencies.json').read_text()):
        check(sha((ROOT/r['path']).read_bytes())==r['sha256'],'read-only cache manifest '+r['path'])
    seal=json.loads((S/'artifact-seal.json').read_text())
    for r in seal:
        p=ROOT/r['path'];check(p.is_file() and sha(p.read_bytes())==r['sha256'] and p.stat().st_size==r['bytes'],'artifact '+r['path'])
    check({r['path'] for r in seal}=={r['path'] for r in records()},'unsealed or missing files')
    counts['sealed_artifacts']=len(seal)
    result={'ok':not failures,'failures':failures,'shared_input_drift':drift,'counts':counts,
            'meaning':'Identity and reproducibility evidence, not an independent mathematical proof/significance review.'}
    (S/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True))
    raise SystemExit(bool(failures))

if __name__=='__main__':main()
