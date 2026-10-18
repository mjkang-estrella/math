#!/usr/bin/env python3
"""Seal the completed T205M manuscript review r1 directory; MIT. Prints the external anchor."""
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from verify import MANIFEST, MANUSCRIPT_ANCHOR, PDF_SHA256, VERDICT, inventory  # noqa: E402


def main():
    files, directories = inventory(ROOT)
    manifest = {'schema': 'T205M-independent-manuscript-review-r1', 'verdict': VERDICT,
                'scope': 'immutable manuscript packet t205m-manuscript-v1 (public article, PDF, code, provenance)',
                'manuscript_anchor': MANUSCRIPT_ANCHOR, 'pdf_sha256': PDF_SHA256,
                'campaign_count_change': False, 'required_repairs': [],
                'files': files, 'directories': directories}
    raw = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
    (ROOT / MANIFEST).write_bytes(raw)
    print(hashlib.sha256(raw).hexdigest())


if __name__ == '__main__':
    main()
