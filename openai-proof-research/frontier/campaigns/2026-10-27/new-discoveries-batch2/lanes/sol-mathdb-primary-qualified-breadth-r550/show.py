import json
from pathlib import Path
D=Path(__file__).parent
for x in json.loads((D/'assigned-records.json').read_text()):
 v=x['record'];print(v['mathdb_id'],v['statement'],'\nSOURCE',v['source_url'],'\n')
