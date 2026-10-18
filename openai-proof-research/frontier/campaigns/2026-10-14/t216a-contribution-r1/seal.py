#!/usr/bin/env python3
# MIT. Writes this review packet's exact inventory; run only on the owned review directory.
import hashlib, importlib.util, json, sys
from pathlib import Path

sys.dont_write_bytecode = True
root = Path(__file__).absolute().parent
spec = importlib.util.spec_from_file_location('review_verify', root / 'verify.py')
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)
b = (json.dumps(v.inventory(root), sort_keys=True, indent=2) + '\n').encode()
(root / 'manifest.json').write_bytes(b)
print(hashlib.sha256(b).hexdigest())
