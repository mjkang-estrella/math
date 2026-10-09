#!/usr/bin/env python3
import pathlib,json,hashlib,sys
R=pathlib.Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i07_structures_novelty_r3'; E=pathlib.Path(__file__).resolve().parent; M=S/'artifact-manifest.json'
review=R/'frontier/reviews/i07-structures-novelty-r3.md'
def record(p):
 b=p.read_bytes();return {'path':str(p.relative_to(R)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def scope(): return sorted([review]+[p for d in [S,E] for p in d.rglob('*') if p.is_file() and p!=M],key=str)
if '--verify' in sys.argv:
 m=json.loads(M.read_text()); assert {x['path'] for x in m['artifacts']}=={str(p.relative_to(R)) for p in scope()},'Artifact inventory changed'
 for x in m['artifacts']+m['dependencies']: assert record(R/x['path'])==x,x['path']
 print(json.dumps({'status':'PASS','artifacts':len(m['artifacts']),'dependencies':len(m['dependencies']),'report_sha256':record(review)['sha256']}))
else:
 deps={x['path'] for x in json.loads((S/'input-hashes.json').read_text())}
 deps|={x['path'] for x in json.loads((S/'pinned-verification.json').read_text())['files']}
 for x in json.loads((S/'retained-literature-verification.json').read_text()): deps|={x['file'],str(pathlib.Path(x['file']).with_suffix('.txt'))}
 m={'algorithm':'SHA-256','self_excluded':str(M.relative_to(R)),'artifacts':[record(p) for p in scope()],'dependencies':[record(R/p) for p in sorted(deps)]}
 M.write_text(json.dumps(m,indent=2)+'\n'); print('Sealed',len(m['artifacts']),'artifacts and',len(m['dependencies']),'dependencies.')
