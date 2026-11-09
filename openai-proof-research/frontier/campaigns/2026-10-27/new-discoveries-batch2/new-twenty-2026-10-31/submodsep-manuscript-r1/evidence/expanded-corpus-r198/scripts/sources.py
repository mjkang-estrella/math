import pathlib,json,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
rows=json.loads((D/'reservation.json').read_text())['rows']
for r in rows[int(sys.argv[1]):int(sys.argv[2])]:
 z=fetch(r['source_url'],str(r['mathdb_id'])+'-abs');print(r['mathdb_id'],z['status'],z.get('body'))
