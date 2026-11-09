import json
from pathlib import Path
L=Path(__file__).parent
rows=json.loads((L/'records.json').read_text())
for n,x in enumerate(rows,1):
 r=x['record']; print(n,r['mathdb_id'],r['title']);print(r['statement']); print('SOURCE:',r['source_name'],r['source_url']);print()
