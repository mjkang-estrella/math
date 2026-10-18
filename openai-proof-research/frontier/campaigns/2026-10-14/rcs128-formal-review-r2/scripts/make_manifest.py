#!/usr/bin/env python3
"""Write manifest.json for the review r2 packet using verify.py's inventory; MIT, Myeongjin Kang."""
import importlib.util
import json
from pathlib import Path
import sys

root = Path(sys.argv[1]).absolute()
spec = importlib.util.spec_from_file_location('packet_verify', root / 'verify.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
(root / 'manifest.json').write_text(json.dumps(module.inventory(root), indent=2) + '\n')
