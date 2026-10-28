#!/usr/bin/env python3
import os, subprocess, sys
from pathlib import Path
packages=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
env=dict(os.environ)
env['LEAN_PATH']=str(Path.cwd())+':'+':'.join(str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if (p/'.lake/build/lib/lean').is_dir())
raise SystemExit(subprocess.run(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean',*sys.argv[1:]],env=env).returncode)
