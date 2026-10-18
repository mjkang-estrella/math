#!/usr/bin/env python3
# MIT. Writes manifest.json for this directory and prints its SHA256 (report externally).
import hashlib, json, sys
from pathlib import Path
sys.dont_write_bytecode = True
from verify import inventory

root = Path(__file__).absolute().parent
b = (json.dumps(inventory(root), sort_keys=True, indent=2) + '\n').encode()
(root / 'manifest.json').write_bytes(b)
print(hashlib.sha256(b).hexdigest())
