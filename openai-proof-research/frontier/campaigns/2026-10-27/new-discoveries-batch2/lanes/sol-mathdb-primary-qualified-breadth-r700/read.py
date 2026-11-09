from pathlib import Path
import json,sys
D=Path(__file__).parent; rows=json.loads((D/'literal-records.json').read_text())
for x in rows[int(sys.argv[1]):int(sys.argv[2])]:
 r=x['record']; print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'])
