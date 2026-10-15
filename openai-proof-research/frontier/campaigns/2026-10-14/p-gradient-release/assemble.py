#!/usr/bin/env python3
"""Build a local DRAFT archive from exact, validated publication artifacts.

This does not submit, license, accept, or certify the mathematics. All paths
are explicit or restricted to named author-owned directories. Third-party
papers, caches, credentials and unrelated research are not copied.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[4]
CAMPAIGN = Path('frontier/campaigns/2026-10-14')
ALLOWED = {'.md', '.tex', '.lean', '.json', '.py', '.txt', '.toml', '.diff'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def assemble(destination):
    selected = {}

    def add(relative):
        relative = Path(relative)
        path = ROOT / relative
        if not path.is_file() or path.is_symlink():
            raise ValueError(f'Missing or nonregular input: {relative}')
        if not path.resolve().is_relative_to(ROOT):
            raise ValueError(f'Input escapes project: {relative}')
        selected[relative.as_posix()] = path.read_bytes()

    for name in ['p-gradient-manuscript', 'p-gradient-parent',
                 'p-gradient-proof', 'p-gradient-proof-r2',
                 'p-gradient-contribution-r1', 'p-gradient-manuscript-consolidation']:
        directory = ROOT / CAMPAIGN / name
        if not directory.is_dir():
            raise ValueError(f'Missing publication component: {name}')
        for path in sorted(directory.rglob('*')):
            if path.is_file() and path.suffix in ALLOWED and '__pycache__' not in path.parts:
                add(path.relative_to(ROOT))
    add(CAMPAIGN / 'p-gradient-manuscript/output/pdf/main.pdf')
    add(CAMPAIGN / 'p-gradient-manuscript/output/pdf/main.log')
    add(CAMPAIGN / 'p-gradient-manuscript-consolidation/build-final.log')
    for path in sorted((ROOT / CAMPAIGN / 'p-gradient-manuscript-consolidation/pages').glob('*.png')):
        add(path.relative_to(ROOT))
    # Explicit review allowlist excludes downloaded third-party articles/text.
    for name in ['review.md', 'source-map.md', 'input-hashes.json', 'supplemental-input-hashes.json',
                 'outputs.json', 'checks/run_checks.py', 'checks/run-output.json',
                 'checks/presentation.json', 'checks/ScalarAudit.lean',
                 'checks/VectorAudit.lean', 'checks/scalar-lean-audit.txt',
                 'checks/lean-audit.txt']:
        add(CAMPAIGN / 'p-gradient-manuscript-review-r1' / name)
    for name in ['lemma.md', 'insertion.md', 'reading.md', 'manifest.json']:
        add(CAMPAIGN / 'p-gradient-uniformity' / name)
    for name in ['README.md', 'Audit.lean', 'FrontierSupport.lean',
                 'FrontierSupport/LiftedEllipticity.lean',
                 'FrontierSupport/VectorEllipticity.lean', 'validation.json',
                 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
        add(CAMPAIGN / 'formal' / name)
    for name in ['sources/upstream.json',
                 'frontier/experiments/i345_lifted_p_gradient_research/analysis.md',
                 'frontier/experiments/i236_viscous_contact_propagation/analytic-attempt.md',
                 'frontier/experiments/i239_viscous_rigidity_proof/analytic-check.md',
                 'frontier/reviews/i239-viscous-rigidity-proof.md',
                 'frontier/iterations/i239-viscous-proof-parent-disposition.md']:
        add(name)
    add(CAMPAIGN / 'p-gradient-release/assemble.py')
    add(CAMPAIGN / 'p-gradient-release/verify_bundle.py')

    # Bind both the PDF/TeX and the actual formal proof bytes to their receipts.
    for component in ['p-gradient-manuscript', 'formal']:
        receipt_path = (CAMPAIGN / component / 'validation.json').as_posix()
        receipt = json.loads(selected[receipt_path])
        for relative, expected in receipt['sha256'].items():
            key = (CAMPAIGN / component / relative).as_posix()
            if key not in selected or digest(selected[key]) != expected:
                raise ValueError(f'Stale or incomplete {component} receipt: {key}')
    # Original proof evidence must stay intact even after manuscript edits.
    proof_receipt = json.loads(selected[(CAMPAIGN / 'p-gradient-proof-r2/input-hashes.json').as_posix()])
    for key, record in proof_receipt['files']['repaired_argument'].items():
        if key not in selected or digest(selected[key]) != record['sha256']:
            raise ValueError(f'Changed reviewed argument: {key}')
    review_base = CAMPAIGN / 'p-gradient-manuscript-review-r1'
    review_outputs = json.loads(selected[(review_base / 'outputs.json').as_posix()])
    for name, record in review_outputs['authored_outputs'].items():
        key = (review_base / name).as_posix()
        if key not in selected or digest(selected[key]) != record['sha256']:
            raise ValueError(f'Changed manuscript review output: {key}')
    for key, record in json.loads(selected[(review_base / 'input-hashes.json').as_posix()]).items():
        if digest((ROOT / key).read_bytes()) != record['sha256']:
            raise ValueError(f'Changed manuscript review input: {key}')

    # Catch concurrent writes; the archive itself uses the captured bytes.
    for key, data in selected.items():
        if (ROOT / key).read_bytes() != data:
            raise ValueError(f'Input changed while assembling: {key}')
    context_commit = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    manifest = {
        'status': 'PUBLICATION DRAFT: authors/license unset; not submitted or published',
        'research_status': 'See included independent reviews and parent disposition; assembly itself makes no acceptance decision.',
        'title': 'Uniform interior gradient estimates for finite p through a constrained affine lift',
        'context_commit': context_commit,
        'commit_note': 'Context only. Individual hashes, not this commit, identify packaged bytes.',
        'authors': None, 'license': None, 'doi': None,
        'formal_coverage': 'Zero-jet ellipticity supporting lemmas only; no full PDE formalization.',
        'files': {key: {'sha256': digest(data), 'bytes': len(data)}
                  for key, data in sorted(selected.items())},
        'external_dependencies': 'Pinned upstream and classical sources remain cited dependencies. Third-party source PDFs and Lean caches are not bundled.',
    }
    selected['BUNDLE-MANIFEST.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
    selected['BUNDLE-README.txt'] = b'''DRAFT RESEARCH PACKAGE -- NOT PUBLICLY SUBMITTED OR PUBLISHED

Read frontier/campaigns/2026-10-14/p-gradient-manuscript/README.md first.
The PDF is in that directory's output/pdf/main.pdf.
Proof and contribution reviews are separate supporting evidence.
The independent manuscript review is included with its exact scope.
Final metadata and publication remain outstanding. Frozen historical
manuscript banners and receipts describe their status before that review.

To rebuild supporting Lean lemmas, install the pinned Lean toolchain, then:
  cd frontier/campaigns/2026-10-14/formal
  lake update
  lake build
  lake env lean Audit.lean
Network access is needed for the pinned dependencies/cache on a clean machine.
The Lean project does not formalize the full analytic theorem.

To typeset the manuscript, run in p-gradient-manuscript with Tectonic 0.17.0:
  tectonic -X compile main.tex --outdir output/pdf --keep-logs

Run the standard-library algebra checks from the extracted package root:
  python3 -I frontier/campaigns/2026-10-14/p-gradient-release/verify_bundle.py
This verifies the package manifest and invokes both recorded checkers.
These include finite sampled inequalities, not solely symbolic proofs.

The original manuscript-review runner records its original workspace
toolchain/cache paths. It is evidence of that run, not a clean-machine
installer. Use the lake commands above for a portable Lean rebuild.

BUNDLE-MANIFEST.json binds every project file by SHA256 and byte length.
Original review inputs and later manuscript revisions are both retained.
Some research notes link to external source scans not bundled here; their
source URLs and recorded hashes are reference metadata, not included files.
No license or author identity has been selected on the user's behalf.
'''
    destination = destination.resolve()
    if destination.exists():
        raise ValueError(f'Refusing to replace existing archive: {destination}')
    destination.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(destination, 'x', compression=zipfile.ZIP_DEFLATED) as archive:
        for key, data in sorted(selected.items()):
            info = zipfile.ZipInfo(key, date_time=(2026, 10, 14, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
    with zipfile.ZipFile(destination) as archive:
        if archive.testzip() is not None:
            raise ValueError('ZIP integrity failure')
        for key, data in selected.items():
            if archive.read(key) != data:
                raise ValueError(f'Archive mismatch: {key}')
    print(json.dumps({'archive': str(destination), 'sha256': digest(destination.read_bytes()),
                      'project_files': len(manifest['files']), 'status': manifest['status']}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='New local ZIP path')
    assemble(parser.parse_args().output)
