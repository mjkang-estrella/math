from pathlib import Path
import json
p=Path(__file__).parent/'frozen/01-moment-witness.json'
d=json.loads(p.read_text())
print({k: (list(v[0]) if isinstance(v,list) and v and isinstance(v[0],dict) else list(v) if isinstance(v,dict) else len(v) if isinstance(v,list) else str(v)[:60]) for k,v in d.items()})
