#!/usr/bin/env python3
"""Independent read-only r678 verifier. Always run using verify.sh's fixed guard."""
from pathlib import Path
import json, hashlib, sys, copy
O=Path(__file__).resolve().parent
I=O.parent/'root-mathdb-breadth-intake-r677'
R=O.parent/'pi-mathdb-full-corpus-inventory-r301'
def load(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(d): return hashlib.sha256(d).hexdigest()
def check(p,e):
    assert p.is_file() and not p.is_symlink(),str(p)
    d=p.read_bytes()
    assert len(d)==e.get('size',e.get('bytes')), 'size mismatch '+str(p)
    assert sha(d)==e['sha256'], 'hash mismatch '+str(p)
def fileset(base):
    return {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}
def manifest_check(base,m,negative=None):
    m=copy.deepcopy(m)
    assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
    if negative=='hash':m['files'][0]['sha256']='0'*64
    if negative=='size':m['files'][0]['size']+=1
    actual=fileset(base)
    if negative=='extra':actual.add('__virtual_unlisted_negative__')
    names=[e['path'] for e in m['files']]
    assert len(names)==len(set(names))
    assert actual==set(names)|set(m['excluded_exact_paths']), 'extra/missing payload file'
    for e in m['files']:
        p=Path(e['path']);assert not p.is_absolute() and '..' not in p.parts
        check(base/p,e)
def main():
    neg=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
    assert len(sys.argv)==1 or neg in ['hash','size','extra']
    manifest_check(O,load(O/'manifest.json'),neg)
    receipt=load(O/'final-verification-receipt.json');check(O/'manifest.json',receipt['manifest'])
    bound=load(O/'initial-bindings.json')
    assert bound==load(O/'flat-bindings.json')
    for e in bound:check(Path(e['path']),e)
    check(I/'manifest.json',{'size':8716,'sha256':'72e7a774392eff42967e028557e752918a750ccef0dea940938d0cc35e5fb4b5'})
    im=load(I/'manifest.json'); assert fileset(I)=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
    for e in im['files']:check(I/e['path'],e)
    pairs=load(I/'bindings.json')
    for e in pairs:
        for k in ['original','copy']:check(Path(e[k]),e)
    rm=load(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')]
    assert len(chunks)==20 and len(rm['frozen_inputs'])==8
    for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
    reservation=load(I/'reserved-ids-r678.json');ids=reservation['ids'];assert len(ids)==len(set(ids))==50
    assert ids==[x['mathdb_id'] for x in load(I/'queue-r678.json')]
    coverage=set(map(int,load(I/'coverage-delta.json')));assert len(coverage)==7833
    sets=[]
    for a in load(I/'active-breadth-reservations.json'):
        t=set(a['ids']);assert len(t)==50 and not t&coverage and not t&set(reservation['protected_ids'])
        assert all(not t&u for u in sets);sets.append(t)
    assert len(sets)==3 and set(ids) in sets
    check(O/'literal-records.json',load(O/'literal-binding.json'))
    literal=load(O/'literal-records.json');disp=load(O/'dispositions.json')
    assert len(literal)==len(disp)==50
    assert [x['record']['mathdb_id'] for x in literal]==ids==[x['mathdb_id'] for x in disp]
    allowed={'complete','definition-dependent','scope-ambiguous','incomplete'}
    for x,d in zip(literal,disp):
        p=Path(x['chunk']);assert p.parent==R/'corpus'
        # Seek exact assigned line, without interpreting unrelated records.
        with p.open('rb') as f:
            for n,line in enumerate(f,1):
                if n==x['line']:break
            else:raise AssertionError('missing corpus line')
        record=json.loads(line);assert record==x['record']
        canonical=json.dumps(record,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')
        assert sha(canonical)==x['canonical_record_sha256']==d['canonical_record_sha256']
        assert sha(line)==x['literal_line_sha256']==d['literal_line_sha256']
        assert d['statement']==record['statement'] and d['mathdb_id']==record['mathdb_id']
        assert sha(d['statement'].encode())==d['statement_utf8_sha256']
        assert d['chunk']==x['chunk'] and d['line']==x['line']
        assert d['completeness_classification'] in allowed and d['completeness_reason'] and d['quantifiers'] and d['technical_assessment']
        assert d['accepted_credit']==0 and not d['novelty_cleared'] and not d['current_registry_cleared']
    assert load(O/'proposals.json')==[]
    for name in ['source-provenance.json','derivative-bindings.json','image-bindings.json']:
        for e in load(O/name):check(Path(e['path']),e)
    print(json.dumps({'integrity':'PASS','literal_reviews':50,'baseline':7833,'original_chunks':20,'frozen_inputs':8,'direct_pairs':len(pairs),'proposals':0,'mathematical_or_novelty_pass':False}))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
