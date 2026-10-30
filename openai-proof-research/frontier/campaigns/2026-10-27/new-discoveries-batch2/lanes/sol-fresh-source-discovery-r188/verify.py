from pathlib import Path
import hashlib,json,sys,datetime
L=Path(__file__).resolve().parent;R=L.parents[5]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def check(rows,base):
    bad=[p for p,h in rows.items() if not (base/p).is_file() or sha(base/p)!=h]
    assert not bad,bad
    return len(rows)
mode=sys.argv[1]
if mode=='science':
    a=json.loads((L/'scientific-freeze.json').read_text())
    n=check(a['files'],L)
    orig={p:h for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']}
    count=check(orig,R);check(orig,L/'originals')
    extra=json.loads((L/'additional-originals.json').read_text())
    for r in extra:
        assert sha(Path(r['original']))==r['sha256'],r
        assert sha(L/r['copy'])==r['sha256'],r
    receipt=dict(utc=now(),status='PASS',scientific_files=n,originals=count,
                 extra_originals=len(extra),originals_and_copies_unchanged=True)
    (L/'scientific-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt)
elif mode=='final':
    a=json.loads((L/'finalmanifest.json').read_text())
    assert set(a['exclusions'])=={'finalmanifest.json','manifest-verification.json'}
    actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(a['exclusions'])
    assert actual==set(a['files'])
    n=check(a['files'],L)
    check(json.loads((L/'scientific-freeze.json').read_text())['files'],L)
    orig={p:h for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']}
    check(orig,R);check(orig,L/'originals')
    for r in json.loads((L/'additional-originals.json').read_text()):
        assert sha(Path(r['original']))==r['sha256']
        assert sha(L/r['copy'])==r['sha256']
    receipt=dict(utc=now(),status='PASS',manifest_files=n,scientific_and_originals_rechecked=True,
                 manifest_sha256=sha(L/'finalmanifest.json'),exclusions=a['exclusions'])
    (L/'manifest-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt)
else:raise ValueError(mode)
