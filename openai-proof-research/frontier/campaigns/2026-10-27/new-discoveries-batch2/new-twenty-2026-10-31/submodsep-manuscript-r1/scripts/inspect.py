from pathlib import Path
import json,importlib.util
L=Path(__file__).resolve().parents[1];E=L/'evidence/expanded-corpus-r198'
a=json.loads((E/'outputs/submod-dual-compressed.json').read_text());print('SUPPORT:',json.dumps(a['support'],indent=2))
r=json.loads((E/'results.json').read_text());print('RESULT:',json.dumps(r.get('341850') if isinstance(r,dict) else [x for x in r if str(x.get('mathdb_id'))=='341850'],indent=2))
print('DEPENDENCIES:',{s:bool(importlib.util.find_spec(s)) for s in ['reportlab','pypdf','PIL']})
print('PACKET:',*[str(p.relative_to(L/'packet-safe')) for p in (L/'packet-safe').rglob('*') if p.is_file()],sep='\n')
