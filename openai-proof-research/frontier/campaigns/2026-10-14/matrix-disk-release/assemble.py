#!/usr/bin/env python3
"""Assemble the reviewed matrix disk package locally; no public submission.

Copyright 2026 Myeongjin Kang. MIT; see ../matrix-disk-manuscript/LICENSE-code.txt.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[4]
C = Path('frontier/campaigns/2026-10-14')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def assemble(destination):
    selected = {}

    def add(name, expected=None):
        name = PurePosixPath(name)
        if name.is_absolute() or '..' in name.parts:
            raise ValueError(f'Unsafe path: {name}')
        path = ROOT / name
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(ROOT):
            raise ValueError(f'Nonregular input: {name}')
        data = path.read_bytes()
        if expected and (sha(data) != expected['sha256'] or len(data) != expected['bytes']):
            raise ValueError(f'Changed frozen input: {name}')
        selected[str(name)] = data

    # The two frozen manifests describe only author-owned manuscript/review
    # artifacts, including the review's isolated reproduction and all-page QA.
    for component, expected_manifest in [
        ('matrix-disk-manuscript', '5777482c17f9a943422a3ef256d5bbe8e17029732680358d1a25726e358904cd'),
        ('matrix-disk-manuscript-review-r1', 'f6b44ba37987035c500827828102020ab5172208f9ddd64ad71ce10880806ff0'),
        ('matrix-disk-formal-glm-r1', '591da01b56411fd4eadcae87f3a2f896c77bcebe1d49d9106fb53d0877e91d69'),
        ('matrix-disk-formal-review-r1', '75c6b6be28944761fe44f9c91bf8e8063bd98e5dffc11f6670ca310c263bb5dc'),
        ('matrix-disk-formal-v1', '04f67b750a409fab81102c698719d0bb219d1101170939c7d637c8a484f48fdc'),
    ]:
        base = C / component
        manifest_path = base / 'outputs.json'
        add(manifest_path)
        if sha(selected[str(manifest_path)]) != expected_manifest:
            raise ValueError(f'Changed frozen manifest: {component}')
        for record in json.loads(selected[str(manifest_path)])['files']:
            add(base / record['path'], record)

    for component in ['matrix-disk-proof-r1', 'matrix-disk-contribution-r1', 'matrix-disk-discovery']:
        manifest_path = C / component / 'outputs.json'
        add(manifest_path)
        receipt = json.loads(selected[str(manifest_path)])
        records = receipt if isinstance(receipt, list) else receipt['files']
        for record in records:
            # Referenced upstream papers remain external dependencies.
            if component == 'matrix-disk-discovery' and Path(record['path']).name in {'direct.tex', 'structural.tex'}:
                continue
            add(record['path'], record)

    for name in ['sources/upstream.json',
                 'frontier/findings/R024-attained-complete-polynomial-disk-rigidity.md',
                 'frontier/findings/R016-complete-crouzeix-equality.md',
                 'frontier/findings/R019-entangled-complete-crouzeix-equality.md',
                 'frontier/experiments/i245_crouzeix_rigidity_proof/analytic-check.md']:
        add(name)
    add(C / 'publication-metadata.json')
    add(C / 'crouzeix-five/analysis.md')
    for name in ['proof-gate-disposition.md', 'manuscript-gate-disposition.json', 'manuscript-checks.json']:
        add(C / 'matrix-disk-parent' / name)
    for name in ['assemble.py', 'verify_bundle.py', 'README.md', 'STATUS.md', 'mathdb-routing.md']:
        add(C / 'matrix-disk-release' / name)

    metadata = json.loads(selected[str(C / 'publication-metadata.json')])
    manifest = {
        'status': 'LOCAL PUBLICATION DRAFT; no public submission, DOI or external peer review',
        'title': 'Disk rigidity for attained complete polynomial Crouzeix equality',
        'authors': metadata['author_names'], 'affiliations': metadata['affiliations'],
        'paper_license': 'CC-BY-4.0', 'original_code_license': 'MIT', 'doi': None,
        'context_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'commit_note': 'Context only; individual hashes identify the bundled bytes.',
        'current_manuscript': str(C / 'matrix-disk-manuscript/output/pdf/main.pdf'),
        'formal_coverage': 'Three finite real scalar variance supporting declarations independently compiled and axiom-audited; no Hilbert integral, Fatou or full analytic theorem formalization. 33 exact finite checks also included.',
        'files': {name: {'sha256': sha(data), 'bytes': len(data)} for name, data in sorted(selected.items())},
        'external_dependencies': 'Pinned complete Crouzeix/Faber operations and credited Jin geometry; source URLs/hashes retained. Third-party source copies excluded.',
    }
    for name, data in selected.items():
        if (ROOT / name).read_bytes() != data:
            raise ValueError(f'Concurrent input change: {name}')
    selected['BUNDLE-MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    selected['BUNDLE-README.txt'] = (
        'LOCAL PUBLICATION DRAFT -- NOT SUBMITTED\n\n'
        'Read frontier/campaigns/2026-10-14/matrix-disk-release/STATUS.md and README.md.\n'
        'The reviewed PDF is in matrix-disk-manuscript/output/pdf/main.pdf.\n'
        'Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.\n'
        'Finite scalar Lean support included; no full analytic Lean certificate.\n'
        'See matrix-disk-formal-v1/README.md for the pinned Lake rebuild.\n'
        'Verify from this extracted root:\n'
        'python3 -I frontier/campaigns/2026-10-14/matrix-disk-release/verify_bundle.py\n'
    ).encode()
    destination = destination.resolve()
    if destination.exists():
        raise ValueError(f'Refusing to replace archive: {destination}')
    destination.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(destination, 'x', compression=zipfile.ZIP_DEFLATED) as archive:
        for name, data in sorted(selected.items()):
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 14, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
    with zipfile.ZipFile(destination) as archive:
        if archive.testzip() is not None:
            raise ValueError('ZIP integrity failure')
        for name, data in selected.items():
            if archive.read(name) != data:
                raise ValueError(f'Archive bytes differ: {name}')
    print(json.dumps({'archive': str(destination), 'sha256': sha(destination.read_bytes()),
                      'project_files': len(manifest['files']), 'status': manifest['status']}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    assemble(parser.parse_args().output)
