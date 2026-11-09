import json
from pathlib import Path
D=Path(__file__).parent
for x in json.loads((D/'literal-records.json').read_text()):
 r=x['record'];print(r['mathdb_id'],r['statement'])
