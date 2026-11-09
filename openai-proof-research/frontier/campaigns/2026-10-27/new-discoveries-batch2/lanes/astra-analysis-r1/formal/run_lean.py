#!/usr/bin/env python3
"""Run the pinned binary, never shell lean; write only inside this lane."""
import os
from pathlib import Path
import subprocess
import sys

here = Path(__file__).resolve().parent
packages = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env = dict(os.environ)
env['LEAN_PATH'] = str(here) + ':' + ':'.join(
    str(p / '.lake/build/lib/lean') for p in sorted(packages.iterdir())
    if (p / '.lake/build/lib/lean').is_dir())
raise SystemExit(subprocess.run([
    '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean',
    *sys.argv[1:]], cwd=here, env=env).returncode)
