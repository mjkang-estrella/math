#!/usr/bin/env python3
"""Seal the completed T212M manuscript review r2 directory; MIT. Prints the external anchor.
Adapted from ../t212m-manuscript-review-r1/seal.py (only schema/verdict/scope strings changed)."""
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0, str(ROOT))
from verify import MANIFEST, MANUSCRIPT_ANCHOR, VERDICT, inventory  # noqa: E402


def main():
    files, directories = inventory(ROOT)
    manifest = {'schema': 'T212M-independent-manuscript-review-r2', 'verdict': VERDICT,
                'scope': 'frozen t212m-manuscript-v1, AH Sections 6/7/10 proof interfaces only, in conjunction with prior gates',
                'manuscript_anchor': MANUSCRIPT_ANCHOR, 'required_objections': 0,
                'acceptance_or_count_change': False,
                'files': files, 'directories': directories}
    raw = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
    (ROOT / MANIFEST).write_bytes(raw)
    print(hashlib.sha256(raw).hexdigest())


if __name__ == '__main__':
    main()
