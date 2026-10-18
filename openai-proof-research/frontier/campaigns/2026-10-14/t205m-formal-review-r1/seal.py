#!/usr/bin/env python3
"""Seal the completed T205M formal review r1 directory; MIT. Prints the external anchor."""
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from verify import MANIFEST, PACKET_ANCHOR, inventory  # noqa: E402


def main():
    files, directories = inventory(ROOT)
    manifest = {'schema': 'T205M-independent-formal-review-r1', 'verdict': 'PASS_SCOPED_T205M',
                'scope': 'finite-poset support packet t205m-formal-v1 only',
                'packet_anchor': PACKET_ANCHOR, 'full_theorem_formalized': False,
                'files': files, 'directories': directories}
    raw = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
    (ROOT / MANIFEST).write_bytes(raw)
    print(hashlib.sha256(raw).hexdigest())


if __name__ == '__main__':
    main()
