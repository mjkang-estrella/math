#!/usr/bin/env python3
"""Authenticate the terminal independent audit before integrating its final gate."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

OWN=Path(__file__).resolve().parent
BASE=OWN.parent
ROOT=BASE.parents[2]
REVIEW=BASE/'kn-minus-edge-manuscript-review-r2'
sha=lambda b:hashlib.sha256(b).hexdigest()
def save(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')
def record(p):
    b=p.read_bytes()
    return dict(path=p.relative_to(ROOT).as_posix(),bytes=len(b),sha256=sha(b))

def main():
    pins={'output-manifest.json':'34a3b8f3cc99cdebe86aadcb10c483ccc86a55baba3af6491a7f8df9dbe1e607',
          'input-manifest.json':'45dcf2614858f2a8560cc89945b5a52d9c7f94df19312821a25053a4b31228a9',
          'review.md':'ede4c4a0e5c029d1db52d717584e13eb70fe3e5036eba173573cdb52664e04ad'}
    for name,h in pins.items():assert sha((REVIEW/name).read_bytes())==h,name
    manifest=json.loads((REVIEW/'output-manifest.json').read_bytes())
    rows=manifest['files']; names=set()
    for r in rows:
        name=r['path'];p=Path(name)
        assert not p.is_absolute() and '..' not in p.parts and name not in names
        names.add(name);b=(REVIEW/p).read_bytes()
        assert len(b)==r['bytes'] and sha(b)==r['sha256'],name
    assert names|{'output-manifest.json','SHA256SUMS'}=={p.relative_to(REVIEW).as_posix() for p in REVIEW.rglob('*') if p.is_file()}
    assert not any(p.is_symlink() for p in REVIEW.rglob('*'))
    for line in (REVIEW/'SHA256SUMS').read_text().splitlines():
        h,name=line.split('  ',1);assert sha((REVIEW/name).read_bytes())==h
    fixed=[];context=[]
    for r in json.loads((REVIEW/'input-manifest.json').read_bytes())['inputs']:
        p=ROOT/r['path'];b=p.read_bytes()
        if r.get('mutable_context'):
            context.append(dict(path=r['path'],changed=sha(b)!=r['sha256']));continue
        assert len(b)==r['bytes'] and sha(b)==r['sha256'],r['path']
        fixed.append(p)
    protected={p:sha(p.read_bytes()) for p in fixed+list(REVIEW.rglob('*')) if p.is_file()}
    with tempfile.TemporaryDirectory(prefix='crossing-r2-algebra-') as tmp:
        d=Path(tmp);(d/'checks').mkdir();(d/'receipts').mkdir()
        shutil.copy2(REVIEW/'checks/check_attribution_algebra.py',d/'checks')
        run=subprocess.run(['python3','-B',str(d/'checks/check_attribution_algebra.py')],capture_output=True,text=True)
        assert run.returncode==0 and not run.stderr
        assert (d/'receipts/attribution-algebra.json').read_bytes()==(REVIEW/'receipts/attribution-algebra.json').read_bytes()
    assert all(sha(p.read_bytes())==h for p,h in protected.items())
    result=dict(status='PASS_AUTHENTICATED_REVISION',external_pins=pins,review_payload_files=len(rows),
                fixed_input_files=len(fixed),live_context=context,unchanged_observed_files=len(protected),
                algebra_replay='PASS_BYTE_IDENTICAL_RECEIPT',algebra_stdout=run.stdout,
                parent_reading='Complete review, scope/authentication script, sealing script, arithmetic checker and revision documentation read. Independent 43-case and 15-page QA evidence reused honestly.',
                verdict='PASS_REVISION',required_fixes=[],
                optional_O1='Inherited RIGHTS scratch-location wording refers to historical r1 scratch; omitted from r2. Clarified in outer release, frozen reviewed bytes preserved.',
                full_claim_unchanged=True,full_crossing_formalized=False,acceptance_awarded=False)
    out=OWN/'manuscript-review-r2-disposition.json';save(out,result)
    artifacts=[REVIEW/n for n in ['review.md','output-manifest.json','input-manifest.json','README.md','provenance.json',
                'checks/check_attribution_algebra.py','checks/check_verifier.py','receipts/verifier-cases.json',
                'receipts/attribution-algebra.json','receipts/input-audit.json','receipts/unchanged-inputs.json','qa/visual-review.json']]
    artifacts += [out,OWN/'release-fresh-formal.json',OWN/'integrate_revision_r2.py',OWN/'manuscript-review-r2-terminal.json']
    gate=dict(status='ALL_REVIEW_GATES_PASS',verdicts=dict(proof='PASS_FULL_CLAIM_UNDER_STIPULATED_UPSTREAM',
              contribution='SUBSTANTIAL_ONE_PACKAGE',formal='PASS_SCOPED_SUPPORT',manuscript_revision='PASS_REVISION'),
              full_claim_unchanged=True,full_crossing_formalized=False,artifacts=[record(p) for p in artifacts],
              scope='Full ordinary crossing theorem all n>=2; path product all m>=4 and n>=1 edges. One result.',
              acceptance='Final archive reproduction still required; this gate alone does not update count.',uploaded=False)
    save(OWN/'final-review-gate.json',gate)
    print(json.dumps(dict(status=result['status'],files=len(rows),fixed=len(fixed),gate_sha256=sha((OWN/'final-review-gate.json').read_bytes())),indent=2))

if __name__=='__main__':main()
