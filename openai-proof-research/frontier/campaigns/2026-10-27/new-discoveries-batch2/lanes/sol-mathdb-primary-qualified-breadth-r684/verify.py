import argparse,json,hashlib,sys,re
from pathlib import Path

def sha(b): return hashlib.sha256(b).hexdigest()
def read(p): return json.loads(p.read_text())
def check(p,h,n):
    assert p.is_file() and not p.is_symlink(),str(p)
    b=p.read_bytes()
    assert len(b)==n, 'size mismatch: '+str(p)
    assert sha(b)==h, 'hash mismatch: '+str(p)
    return b

def exact(root,manifest,excluded):
    files=manifest['files'];names=[x['path'] for x in files]
    assert len(names)==len(set(names)), 'duplicate manifest paths'
    assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names)
    actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() or p.is_symlink()}
    assert actual-set(excluded)==set(names), 'extra/missing payload: '+str((actual-set(excluded))^set(names))
    for x in files:check(root/x['path'],x['sha256'],x.get('size',x.get('bytes')))

def run(root,expected_hash,expected_size):
    check(root/'manifest.json',expected_hash,expected_size)
    m=read(root/'manifest.json')
    assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
    exact(root,m,m['excluded_exact_paths'])
    refs=read(root/'flat-bindings.json')
    for x in refs:check(Path(x['path']),x['sha256'],x['size'])
    initial=read(root/'initial-bindings.json')
    assert all(x in refs for x in initial)
    by={x['path']:x for x in refs}
    L=Path(__file__).resolve().parent.parent
    # In negative copies, refs anchor the real originals; locate intake from bindings.
    I=Path(next(p for p in by if p.endswith('/root-mathdb-breadth-intake-r683/manifest.json'))).parent
    L=I.parent;R=L/'pi-mathdb-full-corpus-inventory-r301'
    assert by[str(I/'manifest.json')]['sha256']=='4cca6da9c529d655b804df75c02da3181031dd4a70a62b66aaaec26458c64eee'
    exact(I,read(I/'manifest.json'),['manifest.json','verification-receipt.json'])
    pairs=read(I/'bindings.json')
    for x in pairs:
        for k in ['original','copy']:check(Path(x[k]),x['sha256'],x['bytes'])
    inv=read(R/'manifest.json')
    chunks=[x for x in inv['files'] if x['path'].startswith('corpus/')]
    assert len(chunks)==20 and len(inv['frozen_inputs'])==8
    for x in chunks+inv['frozen_inputs']:check(R/x['path'],x['sha256'],x['bytes'])
    for name in ['accepted-exclusions.json','historical-dispositions.json']:
        assert (L/'root-mathdb-accepted-exclusions-r304'/name).read_bytes()==(R/'frozen'/name).read_bytes()
    reserve=read(I/'reserved-ids-r684.json');ids=reserve['ids'];S=set(ids)
    assert len(ids)==len(S)==50 and reserve['coverage_baseline']==7983
    queue=read(I/'queue-r684.json');assert [x['mathdb_id'] for x in queue]==ids
    coverage=set(map(int,read(I/'coverage-delta.json')));assert len(coverage)==7983
    active=read(I/'active-breadth-reservations.json');sets=[set(x['ids']) for x in active]
    assert len(sets)==3 and S in sets
    protected=set(reserve['protected_ids'])
    for i,s in enumerate(sets):
        assert len(s)==50 and not s&coverage and not s&protected
        for t in sets[i+1:]:assert not s&t
    found={}
    for c in chunks:
        p=R/c['path']
        for line,b in enumerate(p.open('rb'),1):
            hit=re.search(rb'"mathdb_id"\s*:\s*(\d+)',b)
            if hit and int(hit[1]) in S:
                a=json.loads(b);id=int(hit[1]);assert id not in found
                found[id]=(a,str(p),line)
    assert set(found)==S
    literals=read(root/'literal-records.json');disp=read(root/'dispositions.json')
    assert len(literals)==len(disp)==50
    assert [x['mathdb_id'] for x in literals]==[x['mathdb_id'] for x in disp]==ids
    cats={}
    for lit,d in zip(literals,disp):
        a,p,line=found[d['mathdb_id']]
        h=sha(json.dumps(a,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
        assert lit['record']==a and lit['chunk']==p and lit['line']==line and lit['canonical_record_sha256']==h
        assert d['statement']==a['statement'] and d['statement_utf8_sha256']==sha(a['statement'].encode())
        assert d['canonical_record_sha256']==h and d['corpus_chunk']==p and d['corpus_line']==line
        c=d['independent_completeness'];assert c in ['complete','definition-dependent','scope-ambiguous','incomplete']
        cats[c]=cats.get(c,0)+1
        assert d['completeness_reason'] and d['technical_assessment_and_quantifiers']
        assert d['accepted_credit']==0 and not d['novelty_cleared'] and not d['current_registry_cleared']
    assert cats=={'complete':22,'definition-dependent':17,'scope-ambiguous':7,'incomplete':4}
    assert read(root/'proposals.json')==[]
    for x in read(root/'source-provenance.json'):
        if 'path' in x:check(root/x['path'],x['sha256'],x['size'])
    for x in read(root/'derivative-bindings.json'):
        check(root/x['path'],x['sha256'],x['size']);assert (root/x['parent']).is_file()
    return {'integrity':'PASS','scientific_or_novelty_pass':False,'records':50,'classifications':cats,'original_chunks_verified':20,'frozen_inputs_verified':8,'direct_pairs_verified':len(pairs),'flat_references_verified':len(refs),'baseline':7983,'proposals':0,'credit':0,'exact_payload':True,'reservation_disjointness':True,'manifest_sha256':expected_hash,'manifest_size':expected_size}

if __name__=='__main__':
    p=argparse.ArgumentParser(description='Read-only verifier; run through fixed helper guard. Pin manifest hash and size from final receipt or handback.')
    p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    p.add_argument('--manifest-sha256',required=True);p.add_argument('--manifest-size',required=True,type=int)
    a=p.parse_args()
    try:print(json.dumps(run(a.root,a.manifest_sha256,a.manifest_size),sort_keys=True))
    except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
