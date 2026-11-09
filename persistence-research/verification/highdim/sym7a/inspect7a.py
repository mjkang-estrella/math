import sys
sys.dont_write_bytecode=True
import collections,json,pathlib
H=pathlib.Path(__file__).resolve().parent
for p in sorted(H.glob('search_*.json')):
 d=json.loads(p.read_text());print(p.name,collections.Counter(x['status'] for x in d.values()),'certs',sum(x['certificates'] for x in d.values()),'open leaves',sum(x['open_leaves'] for x in d.values()))
