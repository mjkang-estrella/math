from pathlib import Path
import json
O=Path(__file__).resolve().parent
for a in json.loads((O/'statements.json').read_text()):
 r=a['record'];print(str(r['mathdb_id'])+' '+r['statement']+'\n')
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 j=json.loads((O.parent/'root-mathdb-accepted-exclusions-r304'/name).read_text());print(name,'structure',type(j).__name__,list(j)[:12] if isinstance(j,dict) else len(j))
print((O.parent/'root-mathdb-cayley-review-intake-r363/disposition.json').read_text())
