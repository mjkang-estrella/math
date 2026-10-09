from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i27_geometric_analysis_discovery';E=ROOT/'frontier/experiments/i27_geometric_analysis_discovery';REPORT=ROOT/'frontier/iterations/i27-geometric-analysis-discovery.md';SEAL=S/'artifact-seal.json'
exclude={SEAL,E/'verification.json',E/'seal-verification.json'}
def files():return sorted({p for d in [S,E] for p in d.rglob('*') if p.is_file() and p not in exclude}|{REPORT})
def row(p):
 b=p.read_bytes();return {'path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
if '--verify' not in sys.argv:
 rows=[row(p) for p in files()];SEAL.write_text(json.dumps({'files':rows,'exclusions':[str(x.relative_to(ROOT)) for x in sorted(exclude)],'external_dependencies':'verify.py checks frozen/live inputs and the entire read-only 9340-text cache against its frozen manifest and complete Git tree.'},indent=2)+'\n');print(json.dumps({'sealed_files':len(rows)}))
else:
 s=json.loads(SEAL.read_text());want={x['path']:x for x in s['files']};got={str(p.relative_to(ROOT)):row(p) for p in files()};errors=[p for p in sorted(set(want)|set(got)) if want.get(p)!=got.get(p)];out={'status':'PASS' if not errors else 'FAIL','sealed_files':len(want),'errors':errors};(E/'seal-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));sys.exit(bool(errors))
