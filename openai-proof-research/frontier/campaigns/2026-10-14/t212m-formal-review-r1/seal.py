#!/usr/bin/env python3
"""Seal the completed T212M formal review r1 directory; MIT. Prints the external anchor.
Adapted from ../t205m-formal-review-r1/seal.py."""
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from verify import MANIFEST, PACKET_ANCHOR, VERDICT, inventory  # noqa: E402


def main():
    files, directories = inventory(ROOT)
    manifest = {'schema': 'T212M-independent-formal-review-r1', 'verdict': VERDICT,
                'scope': 'deterministic finite-change tail support packet t212m-formal-v1 only',
                'packet_anchor': PACKET_ANCHOR, 'full_theorem_formalized': False,
                'acceptance_or_count_change': False,
                'files': files, 'directories': directories}
    raw = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
    (ROOT / MANIFEST).write_bytes(raw)
    print(hashlib.sha256(raw).hexdigest())


if __name__ == '__main__':
    main()
