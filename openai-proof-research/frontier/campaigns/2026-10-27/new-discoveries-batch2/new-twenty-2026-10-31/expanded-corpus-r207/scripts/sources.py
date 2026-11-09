import sys,json,importlib.util
from pathlib import Path
L=Path(__file__).resolve().parents[1]; spec=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py'); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
r=json.loads((L/'reservation.json').read_text())['rows']
for row in r[int(sys.argv[1]):int(sys.argv[2])]: m.fetch(row['source_url'],str(row['mathdb_id'])+'-abs')
