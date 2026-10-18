#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Relocate the authenticated reviewer build to this release's copied inputs."""
import argparse
import hashlib
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE if (HERE / 'frontier').is_dir() else HERE.parents[3]
CAMPAIGN = ROOT / 'frontier/campaigns/2026-10-14'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--cache', type=Path, required=True)
    args = parser.parse_args()
    pins = {
        't027o-formal-review-r1/src/independent_build.py': '90bb62811ce8bdeca0938468d83f293bf560d3e874aea16d85d1cf3967bec637',
        't027o-formal-review-r1/src/T027OReview.lean': '6fffc36ac48aa9426ccbae0f7808b1552a3039d1564b3d9e710fda501529a09a',
        't027o-formal-v1/manifest.json': 'b35948fddec735c7d9f0ed742d8158f4787f571cd69175a01f4db7ce2add46a4',
    }
    for name, digest in pins.items():
        path = CAMPAIGN / name
        if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit('REVIEW_BUILD_REFUSED: frozen input changed: ' + name)
    path = CAMPAIGN / 't027o-formal-review-r1/src/independent_build.py'
    spec = importlib.util.spec_from_file_location('t027o_frozen_reviewer_build', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.INPUT = CAMPAIGN / 't027o-formal-v1'
    old_argv = sys.argv
    try:
        sys.argv = [str(path), '--output', str(args.output.resolve()),
                    '--lean', str(args.lean.resolve()), '--cache', str(args.cache.resolve())]
        module.main()
    finally:
        sys.argv = old_argv


if __name__ == '__main__':
    main()
