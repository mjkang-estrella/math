#!/usr/bin/env python3
"""Copied positive/negative controls for the r104 author identity verifier.

Reviewer helper (t298p-proof-r2). It never writes inside the repository:
the packet, its ignored private inputs and the two source anchor files are
copied into a temporary directory under /var/tmp, which is deleted on exit.
Each negative control must fail with its expected reason substring, not
merely a nonzero exit code. Identity checks only; no mathematical content.
"""
import json, shutil, subprocess, sys, tempfile
from pathlib import Path

REPO = Path(sys.argv[1]).resolve()
ANCHOR = sys.argv[2]
PKT = 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r104'


def build(tmp):
    root = Path(tmp) / 'repo'
    (root / 'sources').mkdir(parents=True)
    for f in ['preprints-tree.json', 'upstream.json']:
        shutil.copy2(REPO / 'sources' / f, root / 'sources' / f)
    shutil.copytree(REPO / PKT, root / PKT, symlinks=True)
    return root


def run(root, anchor):
    p = subprocess.run([sys.executable, '-I', '-B', str(root / PKT / 'verify.py'), '--anchor', anchor,
                        '--repo', str(root)], capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr).strip()


def first_private_source(root):
    s = json.loads((root / PKT / 'source-receipts.json').read_text())
    return root / PKT / 'private' / s['files'][3]['path']


CONTROLS = [
    ('positive', None, 'PASS', True),
    ('wrong_anchor', 'anchor', 'external manifest anchor', False),
    ('altered_candidate', lambda r: (r / PKT / 'candidate.md').open('a').write('\n'), 'payload candidate.md', False),
    ('missing_candidate', lambda r: (r / PKT / 'candidate.md').unlink(), 'exact public membership', False),
    ('extra_public_file', lambda r: (r / PKT / 'extra.md').write_text('x'), 'exact public membership', False),
    ('altered_tree', lambda r: (r / 'sources/preprints-tree.json').open('a').write(' '), 'complete tree anchor', False),
    ('altered_source_body', lambda r: first_private_source(r).open('a').write('%'), 'source SHA', False),
    ('altered_primary_pdf', lambda r: (r / PKT / 'private/primary/shlyakhtenko-relative.pdf').open('ab').write(b'\0'), 'primary shlyakhtenko-relative.pdf', False),
]

results = []
for name, mut, expect, should_pass in CONTROLS:
    with tempfile.TemporaryDirectory(dir='/var/tmp', prefix='t298p-proof-r2-ctl-') as tmp:
        root = build(tmp)
        anchor = ANCHOR
        if mut == 'anchor':
            anchor = '0' * 64
        elif mut is not None:
            mut(root)
        rc, out = run(root, anchor)
        ok = (rc == 0 and expect in out) if should_pass else (rc != 0 and expect in out)
        results.append(dict(control=name, rc=rc, expected_reason=expect, observed=out[-160:], ok=ok))
summary = dict(all_ok=all(r['ok'] for r in results), controls=results,
               scope='identity/integrity controls of the copied author verifier; no mathematical verdict')
print(json.dumps(summary, indent=1))
sys.exit(0 if summary['all_ok'] else 1)
