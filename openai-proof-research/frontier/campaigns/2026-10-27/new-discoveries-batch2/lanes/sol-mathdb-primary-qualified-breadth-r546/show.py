from pathlib import Path
import json
P=Path(__file__).resolve().parent
for i,d in enumerate(json.loads((P/'assigned-records.json').read_text())):
 if 25<=i<37: print('\n',i,d['mathdb_id'],d['record']['title'],'\n',d['statement_utf8'],'\nSOURCE',d['record']['source_url'])
for n in ['adjudications.json','hypothesis-queue.json']:print(n,(P.parent/'root-mathdb-breadth-intake-r545'/n).read_text())
