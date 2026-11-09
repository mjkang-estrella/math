from pathlib import Path
import json
D=Path(__file__).resolve().parent
for x in json.loads((D/'literal-records.json').read_text()):
 r=x['record'];print(r['mathdb_id'],r['statement'],'\nSOURCE',r['source_url'])
