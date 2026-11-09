#!/usr/bin/env python3
import sys,subprocess
from pathlib import Path
p=Path(__file__).resolve().parent
logs=p/'verification/development'; logs.mkdir(parents=True,exist_ok=True)
n=len(list(logs.glob('*.json')))+1
name=Path(sys.argv[1]).stem
log=logs/f'{n:03d}-{name}.log'
raise SystemExit(subprocess.run([sys.executable,'guard.py',str(log),*sys.argv[1:]],cwd=p/'formal').returncode)
