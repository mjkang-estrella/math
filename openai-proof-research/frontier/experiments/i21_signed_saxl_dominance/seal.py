"""Seal the allowed I21 artifacts, excluding seal and derived verification."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i21_signed_saxl_dominance';E=Path(__file__).resolve().parent
files=[R/'frontier/iterations/i21-signed-saxl-dominance.md']+[p for folder in (S,E) for p in folder.rglob('*') if p.is_file() and p.name not in ('artifact-seal.json','verification.json') and '__pycache__' not in p.parts]
a={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
(S/'artifact-seal.json').write_text(json.dumps(dict(pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',files=a),indent=2)+'\n');print('sealed',len(a),'artifacts')
