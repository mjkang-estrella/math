from pathlib import Path
import json
D=Path(__file__).parent
for a in json.loads((D/'literal-records.json').read_text()): print(a['id'],a['record']['statement'],'\n')
