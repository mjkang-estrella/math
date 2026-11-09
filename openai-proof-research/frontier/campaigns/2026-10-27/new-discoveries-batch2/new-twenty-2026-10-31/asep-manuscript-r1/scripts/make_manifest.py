"""Write dossier/MANIFEST.json (SHA-256 of every dossier file). python3 -I make_manifest.py"""
import hashlib, json
from pathlib import Path
D = Path(__file__).resolve().parents[1] / 'dossier'
files = {str(p.relative_to(D)): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in sorted(D.rglob('*')) if p.is_file() and p.name != 'MANIFEST.json' and '__pycache__' not in p.parts}
(D / 'MANIFEST.json').write_text(json.dumps({'description': 'SHA-256 of every file of the source-only dossier', 'files': files}, indent=1) + '\n')
print(len(files))
