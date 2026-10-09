"""Seal or verify the R2 review and every artifact in its authorized directories."""
from pathlib import Path
import sys,json,hashlib,platform
BASE=Path(__file__).resolve().parents[3]
SRC=BASE/'frontier/sources/i17_six_point_ramsey_r2';EXP=BASE/'frontier/experiments/i17_six_point_ramsey_r2';REPORT=BASE/'frontier/reviews/i17-six-point-ramsey-r2.md'
SEAL=SRC/'artifact-manifest.json';OUT=SRC/'verification.json';excluded={SEAL,OUT}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def files():return sorted({p for root in [SRC,EXP] for p in root.rglob('*') if p.is_file() and p not in excluded}|{REPORT})
if '--verify' not in sys.argv:
 data={'schema':1,'assumed_revision':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','candidate_sha256':'87b86401ed5c1d554715c78fa203e33acb0117fd8255357e495a882842c0feb8','verdict':'PASS','python_version':platform.python_version(),'exclusions':[str(p.relative_to(BASE)) for p in sorted(excluded)],'files':[{'path':str(p.relative_to(BASE)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in files()]}
 SEAL.write_text(json.dumps(data,indent=2)+'\n')
data=json.loads(SEAL.read_text());errors=[];actual={str(p.relative_to(BASE)) for p in files()};expected={x['path'] for x in data['files']}
if actual!=expected:errors.append({'file_set_difference':sorted(actual^expected)})
for it in data['files']:
 p=BASE/it['path']
 if not p.is_file() or p.stat().st_size!=it['bytes'] or sha(p)!=it['sha256']:errors.append({'changed_or_missing':it['path']})
inputs=json.loads((SRC/'input-manifest.json').read_text());live_changes=[]
for it in inputs:
 p=BASE/it['path']
 if not p.is_file() or sha(p)!=it['sha256']:live_changes.append(it['path'])
result={'status':'FAIL' if errors else 'PASS','sealed_artifacts':len(data['files']),'errors':errors,'live_inputs_changed_since_r2_freeze':live_changes,'report_sha256':sha(REPORT),'artifact_manifest_sha256':sha(SEAL),'verdict':'PASS','scope':'Artifact integrity; mathematical review is in the sealed report.'}
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));raise SystemExit(bool(errors))
