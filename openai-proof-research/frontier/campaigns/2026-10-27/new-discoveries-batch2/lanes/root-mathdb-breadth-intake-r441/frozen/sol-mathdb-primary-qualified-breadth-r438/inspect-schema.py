from pathlib import Path
import json
L=Path(__file__).resolve().parent.parent
for name in ['pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=json.loads((L/name/'manifest.json').read_text());print(name,list(d)[:8]);print(str((d.get('files',[]) if isinstance(d,dict) else d)[:2]))
for name in ['root-mathdb-breadth-intake-r437/queue.json','root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/disposition.json']:
 d=json.loads((L/name).read_text());print(name,type(d),list(d)[:12] if isinstance(d,dict) else ('length',len(d),'first keys',list(d[0]) if isinstance(d[0],dict) else type(d[0])))
