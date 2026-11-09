from work import *
bindings=[json.loads(s) for s in (L/'bindings.jsonl').read_text().splitlines()]
checks=[]
for r in bindings:
 assert sha(Path(r['copy']))==r['sha256']
 assert sha(Path(r['original']))==r['sha256']
 checks.append({'original':r['original'],'copy':r['copy'],'sha256':r['sha256'],'before_after_equal':True})
dump('source-postread-checks.json',checks)
dump('source-hashes.json',{str(p.relative_to(L)):sha(p) for p in sorted((L/'frozen').glob('*/*'))})
dump('manifest.json',{str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']})
print('manifest and postread source verification complete')
