#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Create the exact manifest only after final author checks and root audit adoption.
Run with python3 -B. The printed digest must be retained outside this package.
"""
import json
from pathlib import Path
from verify import MANIFEST, SCHEMA, inventory, need, parse, root_path, sha, verify


def make_manifest(root, stage):
    files, dirs = inventory(root)
    need(MANIFEST not in files, 'refuse to overwrite an existing seal')
    return {'schema': SCHEMA, 'stage': stage,
            'files': [{'path': p, 'bytes': files[p], 'sha256': sha((root / p).read_bytes())}
                      for p in sorted(files)], 'directories': dirs,
            'limits': 'Integrity only; no mathematical or independent-review verdict.'}


if __name__ == '__main__':
    root = root_path(Path(__file__).absolute().parent)
    status = parse((root / 'final-checkpoint.json').read_bytes())
    need(status['formal_review_adopted_by_root'] is True, 'await root-adopted formal review')
    manifest = root / MANIFEST
    manifest.write_text(json.dumps(make_manifest(root, 'final'), indent=2) + '\n')
    anchor = sha(manifest.read_bytes())
    try:
        result = verify(root, anchor)
    except Exception:
        manifest.unlink()
        raise
    print(json.dumps(result, sort_keys=True))
