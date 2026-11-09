from pathlib import Path
import json
L=Path(__file__).resolve().parent.parent
for pat in ['*r301','*r304','*r363']:
 d=next(L.glob(pat));m=json.loads((d/'manifest.json').read_text());es=m['files'] if isinstance(m,dict) else m
 print(d.name,'keys',list(m) if isinstance(m,dict) else 'list','entrykeys',list(es[0]))
 print('unlisted',sorted({str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-{e['path'] for e in es})[:60]);print('missing', [e['path'] for e in es if not (d/e['path']).exists()][:5])
