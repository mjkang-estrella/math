#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License.
"""Independent byte/scope inventory. Writes only to this review directory."""
from pathlib import Path
import hashlib
import json
import re
import sys

OWN = Path(__file__).resolve().parents[1]
PROJECT = OWN.parents[3]
BASE = OWN.parent
PACKAGE = BASE / 'kn-minus-edge-manuscript-r2'
OLD = BASE / 'kn-minus-edge-manuscript'
sha = lambda b: hashlib.sha256(b).hexdigest()


def record(p, role, extent):
    p = p.resolve()
    data = p.read_bytes()
    return dict(path=p.relative_to(PROJECT).as_posix(), bytes=len(data),
                sha256=sha(data), role=role, read_extent=extent)


def main():
    if '--after' in sys.argv:
        entries = json.loads((OWN/'input-manifest.json').read_text())['inputs']
        mutable=[]
        fixed=0
        for r in entries:
            data = (PROJECT/r['path']).read_bytes()
            if r.get('mutable_context'):
                mutable.append(dict(path=r['path'],initial_bytes=r['bytes'],initial_sha256=r['sha256'],
                                    observed_bytes=len(data),observed_sha256=sha(data),
                                    changed=(len(data)!=r['bytes'] or sha(data)!=r['sha256']),
                                    role='Live orchestration context, excluded from fixed manuscript/proof input invariants'))
                continue
            assert len(data) == r['bytes'] and sha(data) == r['sha256'], r['path']
            fixed+=1
        result = dict(status='PASS_UNCHANGED',fixed_files=fixed,total_input_records=len(entries),
                      manuscript_directory_edited=False,all_fixed_inputs_unchanged=True,
                      live_context_records=mutable)
        (OWN/'receipts/unchanged-inputs.json').write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(result))
        return

    manifest_bytes = (PACKAGE/'output-manifest.json').read_bytes()
    assert sha(manifest_bytes) == 'ffb8d4f9b4e634375b59c4b73db503c8d1a46a5ecb4862601cd728f4b7606027'
    manifest = json.loads(manifest_bytes)  # authenticate before parsing
    for r in manifest['files']:
        p = Path(r['path'])
        assert not p.is_absolute() and '..' not in p.parts
        data = (PACKAGE/p).read_bytes()
        assert len(data) == r['bytes'] and sha(data) == r['sha256'], str(p)
    actual = {p.relative_to(PACKAGE).as_posix() for p in PACKAGE.rglob('*') if p.is_file()}
    assert actual == {r['path'] for r in manifest['files']} | {'output-manifest.json','SHA256SUMS'}
    assert not any(p.is_symlink() for p in PACKAGE.rglob('*'))
    refs = json.loads((PACKAGE/'input-manifest.json').read_text())['inputs']
    for r in refs:
        data = (PROJECT/r['path']).read_bytes()
        assert len(data) == r['bytes'] and sha(data) == r['sha256'], r['path']
    protected = json.loads((BASE/'kn-minus-edge-parent/manuscript-r2-before.json').read_text())
    for name,h in protected.items():
        assert sha((PROJECT.parent/name).read_bytes()) == h, name

    a = (OLD/'main.tex').read_bytes(); b = (PACKAGE/'main.tex').read_bytes()
    start = b'\\section{Conventions and upstream statements}'
    end = b'\\section{Novelty boundary}'
    old_proof = a[a.index(start):a.index(end)]
    new_proof = b[b.index(start):b.index(end)]
    assert old_proof == new_proof
    blocks = {}
    for env in ['maintheorem','maincorollary']:
        pattern = rb'\\begin\{'+env.encode()+rb'\}.*?\\end\{'+env.encode()+rb'\}'
        first = re.findall(pattern,a,re.S); second = re.findall(pattern,b,re.S)
        assert len(first) == len(second) == 1 and first == second
        blocks[env] = dict(bytes=len(first[0]), sha256=sha(first[0]), byte_identical=True)
    inherited = ['support/release_checks.py','support/run_all.py','support/build.py']
    inherited += [p.relative_to(OLD).as_posix() for p in (OLD/'support/inherited').rglob('*') if p.is_file()]
    inherited += ['checks/'+name for name in ['run-receipt.json','run-receipt-large.json',
                  'release_checks.out','release_checks.json','author-checks.out',
                  'author-modp.out','reviewer-adversarial.out','reviewer-adversarial.json']]
    for name in inherited:
        assert (OLD/name).read_bytes() == (PACKAGE/name).read_bytes(), name
    core = BASE/'kn-minus-edge-formal-v1/KnMinusEdge.lean'
    source = core.read_text()
    decls = re.findall(r'^\s*(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|def)\s+(\w+)',source,re.M)
    counts = {kind:sum(k==kind for k,n in decls) for kind in ('theorem','def')}
    assert counts == {'theorem':47,'def':17}, counts
    for filename,count in [('kn-minus-edge-formal-v1/Controls.lean',9),('kn-minus-edge-formal-review-r1/ReviewControls.lean',16)]:
        assert len(re.findall(r'^theorem\s+', (BASE/filename).read_text(), re.M)) == count
    assert sha((BASE/'kn-minus-edge-formal-review-r1/review.md').read_bytes()) == 'bbb0344dda8194ef776a8c4bc68a8d44894e6cee178fe019a78cfd962f4d3773'
    result = dict(status='PASS', authenticated_output_records=len(manifest['files']),
                  exact_r2_file_count=len(actual), authenticated_referenced_inputs=len(refs),
                  protected_historical_files=len(protected),
                  proof_sections_2_to_6=dict(bytes=len(old_proof),sha256=sha(old_proof),byte_identical=True),
                  statement_blocks=blocks, unchanged_scripts_and_runs=inherited,
                  formal_source_declaration_counts=counts, author_controls=9, independent_controls=16)
    (OWN/'receipts/input-audit.json').write_text(json.dumps(result,indent=2)+'\n')

    records = {}
    def add(p,role,extent):
        r=record(p,role,extent); records[r['path']]=r
    for name in protected:
        add(PROJECT.parent/name,'frozen historical protected input','bytes authenticated; no fresh proof/build conclusion')
    for r in refs:
        add(PROJECT/r['path'],'referenced r2 input','hash/size authenticated; inherited reading claims not recast as current reading')
    for p in PACKAGE.rglob('*'):
        if p.is_file(): add(p,'frozen r2 package','bytes authenticated; documentation/source diff and verifier read; PDF rendered independently')
    extras = {
      'kn-minus-edge-manuscript-review-r1/review.md':'full',
      'kn-minus-edge-manuscript-review-r1/provenance.json':'full',
      'kn-minus-edge-parent/manuscript-review-r1-disposition.md':'full',
      'kn-minus-edge-parent/manuscript-r2-disposition.json':'full',
      'kn-minus-edge-parent/manuscript-r2-verification.json':'full',
      'kn-minus-edge-parent/check_manuscript_r2.py':'full inspection; not executed',
      'kn-minus-edge-parent/manuscript-r2-before.json':'full inventory used to authenticate 271 historical files',
      'kn-minus-edge-formal-review-r1/review.md':'full; prior compiler findings reused as historical evidence',
      'kn-minus-edge-formal-v1/coverage.json':'full',
      'kn-minus-edge-formal-v1/KnMinusEdge.lean':'all declaration counts; relevant conditional types and U4/localization/descent interfaces',
      'kn-minus-edge-formal-v1/Controls.lean':'declaration counts and control signatures',
      'kn-minus-edge-formal-review-r1/ReviewControls.lean':'declaration counts and control signatures',
      'kn-minus-edge-parent/formal-review-r1-disposition.json':'full'
    }
    for name,extent in extras.items(): add(BASE/name,'independent revision audit evidence',extent)
    for p in (BASE/'kn-minus-edge-parent').glob('*task*.json'):
        add(p,'orchestration attribution context','JSON headers only; not a mathematical or compiler premise')
    add(PROJECT/'AGENTS.md','project instructions','full')
    for r in records.values():
        if r['role']=='orchestration attribution context':r['mutable_context']=True
    output = dict(schema=1,root=str(PROJECT),role='Independent focused revision audit, round 2',
                  policy='Referenced in place; no third-party reading material copied. Authentication is not a claim of fresh semantic reading.',
                  inputs=sorted(records.values(),key=lambda r:r['path']))
    (OWN/'input-manifest.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='unchanged_scripts_and_runs'},indent=2))


if __name__ == '__main__': main()
