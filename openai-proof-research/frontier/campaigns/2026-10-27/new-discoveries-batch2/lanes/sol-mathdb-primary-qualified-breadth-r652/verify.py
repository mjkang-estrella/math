#!/usr/bin/env python3
"""Independent read-only verification. Run through verify.sh (fixed resource guard)."""
import hashlib,json,pathlib,re,sys,datetime
HERE=pathlib.Path(__file__).resolve().parent
INTAKE=HERE.parent/'root-mathdb-breadth-intake-r651'
CORPUS=HERE.parent/'pi-mathdb-full-corpus-inventory-r301'
EXCLUDED={'manifest.json','final-verification-receipt.json'}
def digest(z):return hashlib.sha256(z).hexdigest()
def load(p):return json.loads(p.read_text())
def check_bytes(z,r):
    if len(z)!=r.get('size',r.get('bytes')):raise ValueError('size mismatch')
    if digest(z)!=r['sha256']:raise ValueError('hash mismatch')
def check_file(p,r):
    if p.is_symlink():raise ValueError('symlink '+str(p))
    check_bytes(p.read_bytes(),r)
def exact_set(actual,expected):
    if actual!=expected:raise ValueError('extra/missing files '+str(actual^expected))
def canonical(r):return digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
def run():
    own=load(HERE/'manifest.json');expected={r['path'] for r in own['files']}
    actual={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file()}
    if '--negative-extra' in sys.argv:actual.add('UNEXPECTED.bin')
    exact_set(actual-EXCLUDED,expected)
    for r in own['files']:
        if r['path']=='proposals.json' and '--negative-hash' in sys.argv:
            z=(HERE/r['path']).read_bytes();check_bytes(bytes([z[0]^1])+z[1:],r)
        if r['path']=='proposals.json' and '--negative-size' in sys.argv:check_bytes((HERE/r['path']).read_bytes()+b'x',r)
        check_file(HERE/r['path'],r)
    refs=load(HERE/'flat-bindings.json')
    for r in refs:check_file(pathlib.Path(r['path']),r)
    initial={r['path']:r for r in load(HERE/'initial-bindings.json')}
    for name in ['manifest.json','queue-r652.json','reserved-ids-r652.json','coverage-delta.json','adjudications.json','hypothesis-queue.json','verification-receipt.json','bindings.json']:
        check_file(INTAKE/name,initial[str((INTAKE/name).resolve())])
    im=load(INTAKE/'manifest.json');iex={r['path'] for r in im['files']}
    exact_set({str(p.relative_to(INTAKE)) for p in INTAKE.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'},iex)
    for r in im['files']:check_file(INTAKE/r['path'],r)
    pairs=load(INTAKE/'bindings.json')
    for r in pairs:
        for k in ['original','copy']:check_file(pathlib.Path(r[k]),r)
    inv=load(CORPUS/'manifest.json')
    pair=[r for r in pairs if r['original']==str(CORPUS/'manifest.json')]
    assert len(pair)==1
    check_file(CORPUS/'manifest.json',pair[0])
    chunks=[r for r in inv['files'] if r['path'].startswith('corpus/')]
    assert len(chunks)==20 and len(inv['frozen_inputs'])==8
    for r in chunks+inv['frozen_inputs']:check_file(CORPUS/r['path'],r)
    coverage=set(map(int,load(INTAKE/'coverage-delta.json')));assert len(coverage)==7183
    reservations=load(INTAKE/'active-breadth-reservations.json');seen=set()
    assert len(reservations)==3
    for r in reservations:
        s=set(r['ids']);assert len(s)==50 and not s&seen and not s&coverage and not s&set(r['protected_ids']);seen|=s
    reserved=load(INTAKE/'reserved-ids-r652.json');ids=reserved['ids']
    assert reserved['coverage_baseline']==7183 and reserved['lane']==HERE.name
    assert [r['mathdb_id'] for r in load(INTAKE/'queue-r652.json')]==ids
    assert next(r for r in reservations if r['lane']==HERE.name)['ids']==ids
    literals=load(HERE/'literal-records.json');disps=load(HERE/'dispositions.json')
    assert len(literals)==len(disps)==len(set(ids))==50
    assert [r['mathdb_id'] for r in literals]==[r['mathdb_id'] for r in disps]==ids
    for a,d in zip(literals,disps):
        p=pathlib.Path(a['corpus_chunk']);assert p in {CORPUS/r['path'] for r in chunks}
        with p.open() as f:
            for n,line in enumerate(f,1):
                if n==a['corpus_line']:original=json.loads(line);break
            else:raise ValueError('missing corpus line')
        assert original==a['record'] and original['mathdb_id']==a['mathdb_id']
        assert canonical(original)==a['canonical_record_sha256']==d['canonical_record_sha256']
        assert original['statement']==d['literal_statement_utf8']
        assert digest(original['statement'].encode())==d['statement_utf8_sha256']
        assert d['statement_completeness'] in {'complete','definition-dependent','scope-ambiguous','incomplete'}
        assert d['completeness_reason'] and d['technical_assessment'] and d['accepted_credit']==0
        assert not d['current_registry_cleared'] and not d['full_dependency_audit']
    assert len(load(HERE/'proposals.json'))<=3
    for r in load(HERE/'source-provenance.json'):
        if 'path' in r:check_file(HERE/r['path'],r)
    # Bounded negatives use the same byte/set validators with virtual damaged inputs.
    # They do not mutate an original, derivative, or manifest.
    sample=next(r for r in own['files'] if r['path']=='proposals.json');z=(HERE/sample['path']).read_bytes()
    rejected=[]
    for name,fn in [('hash',lambda:check_bytes(bytes([z[0]^1])+z[1:],sample)),('size',lambda:check_bytes(z+b'x',sample)),('extra-file',lambda:exact_set(expected|{'UNEXPECTED.bin'},expected))]:
        try:fn()
        except ValueError:rejected.append(name)
        else:raise ValueError('negative accepted '+name)
    receipt=HERE/'final-verification-receipt.json'
    if receipt.exists():
        rr=load(receipt);check_file(HERE/'manifest.json',rr['manifest'])
    return dict(integrity='PASS',scientific_acceptance=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),literal_reviews=50,baseline=7183,proposals=len(load(HERE/'proposals.json')),original_chunks=20,frozen_inputs=8,direct_pairs=len(pairs),reservation_sets=3,disjointness=True,negative_rejections=rejected,manifest=dict(sha256=digest((HERE/'manifest.json').read_bytes()),size=(HERE/'manifest.json').stat().st_size))
if __name__=='__main__':
    try:print(json.dumps(run(),indent=2))
    except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
