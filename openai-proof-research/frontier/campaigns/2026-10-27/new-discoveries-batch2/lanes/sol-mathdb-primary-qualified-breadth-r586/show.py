from pathlib import Path
import json
D=Path(__file__).parent
for x in json.loads((D/'literal-records.json').read_text()):
 print(x['id'],x['record']['statement'])
