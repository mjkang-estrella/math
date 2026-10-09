from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i17_six_point_ramsey_novelty_r3'
E=Path(__file__).resolve().parent
REPORT=ROOT/'frontier/reviews/i17-six-point-ramsey-novelty-r3.md'
MANIFEST=S/'artifact-manifest.json'
VERIFICATION=S/'seal-verification.json'
def entry(p):
    b=p.read_bytes();return {'path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def paths():return sorted({REPORT}|{p for d in [S,E] for p in d.rglob('*') if p.is_file() and p not in [MANIFEST,VERIFICATION] and '__pycache__' not in p.parts})
if '--verify' in sys.argv:
    m=json.loads(MANIFEST.read_text());assert {x['path'] for x in m['files']}=={str(p.relative_to(ROOT)) for p in paths()},'Artifact inventory changed'
    for i in m['files']+m['external_dependencies']:
        assert entry(ROOT/i['path'])=={k:i[k] for k in ['path','bytes','sha256']},i['path']
    out={'status':'PASS','sealed_artifacts':len(m['files']),'external_dependencies':len(m['external_dependencies']),'manifest_sha256':hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),'scope':'Retained artifact and dependency integrity. Dynamic live input drift is checked separately by verify_provenance.py.'}
    VERIFICATION.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
else:
    deps=json.loads((S/'external-dependencies.json').read_text())
    MANIFEST.write_text(json.dumps({'schema':1,'verdict':'TECHNICAL ONLY','proof_status':'PASS retained, no repairs','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','exclusions':[str(p.relative_to(ROOT)) for p in [MANIFEST,VERIFICATION]],'files':[entry(p) for p in paths()],'external_dependencies':list(deps.values())},indent=2)+'\n')
    print('Sealed',len(paths()),'artifacts and',len(deps),'external dependencies.')
