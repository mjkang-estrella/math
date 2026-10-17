#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Exercise the read-only verifier on an isolated, fully prepared fixture."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    files = [p.relative_to(ROOT) for p in ROOT.rglob('*') if p.is_file()
             and p.name != 'output-manifest.json' and 'tmp' not in p.relative_to(ROOT).parts]
    tmp = ROOT / 'tmp'
    need_new = not tmp.exists()
    if not need_new:
        raise RuntimeError('Temporary workspace must not already exist')
    fixture = tmp / 'integrity-fixture'
    fixture.mkdir(parents=True)
    rows = []
    try:
        for rel in files:
            dst = fixture / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, dst)
        manifest = {'schema': 'O217-manuscript-r1', 'full_theorem_formalized': False,
                    'independent_manuscript_verdict': False,
                    'files': [{'path': str(r), 'sha256': sha(fixture / r),
                               'bytes': (fixture / r).stat().st_size} for r in sorted(files)],
                    'directories': sorted(str(p.relative_to(fixture)) for p in fixture.rglob('*') if p.is_dir())}
        mp = fixture / 'output-manifest.json'
        mp.write_text(json.dumps(manifest, indent=2) + '\n')
        anchor = sha(mp)

        def run(name, a=anchor, ok=False):
            r = subprocess.run([sys.executable, '-B', str(ROOT / 'verify.py'),
                                '--root', str(fixture), '--anchor', a], capture_output=True, text=True)
            if (r.returncode == 0) != ok:
                raise RuntimeError(name + ': unexpected result: ' + r.stdout + r.stderr)
            rows.append(dict(name=name, exit_code=r.returncode, stdout=r.stdout, stderr=r.stderr))

        run('intact fixture', ok=True)
        run('wrong external anchor', '0' * 64)
        target = fixture / 'main.tex'
        original = target.read_bytes()
        target.write_bytes(original + b'\n% altered\n')
        run('changed manuscript')
        target.write_bytes(original)
        target.unlink()
        run('missing manuscript')
        target.write_bytes(original)
        extra = fixture / 'unexpected.txt'
        extra.write_text('extra')
        run('extra file')
        extra.unlink()
        empty = fixture / 'unexpected-empty'
        empty.mkdir()
        run('extra empty directory')
        empty.rmdir()
        target.unlink()
        target.symlink_to(ROOT / 'main.tex')
        run('symlinked manuscript')
        target.unlink()
        target.write_bytes(original)
        pdf = fixture / 'output/pdf/fourth-moment-sk-comparison.pdf'
        pdf.write_bytes(pdf.read_bytes() + b'\nchanged')
        run('changed PDF')
        # Re-anchoring an incoherent fixture must still fail its semantic binding.
        for row in manifest['files']:
            if row['path'] == str(pdf.relative_to(fixture)):
                row.update(sha256=sha(pdf), bytes=pdf.stat().st_size)
        mp.write_text(json.dumps(manifest, indent=2) + '\n')
        run('reanchored PDF with stale QA', sha(mp))
        receipt = dict(status='PASS_INTEGRITY_CONTROLS', scope='Isolated copy; no mathematical verdict',
                       controls=rows, verifier_sha256=sha(ROOT / 'verify.py'))
        (ROOT / 'checks/integrity-controls.json').write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({'status': receipt['status'], 'controls': len(rows)}))
    finally:
        shutil.rmtree(tmp)


if __name__ == '__main__':
    main()
