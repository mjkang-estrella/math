"""Print selected entries of another lane's results.json (read-only). usage: showresults.py FILE maxchars id1 id2 ..."""
import json, sys
path, mx = sys.argv[1], int(sys.argv[2])
want = set(sys.argv[3:])
d = json.load(open(path))
items = d.values() if isinstance(d, dict) else d
if isinstance(d, dict) and 'results' in d:
    items = d['results']
    items = items.values() if isinstance(items, dict) else items
for o in items:
    if not isinstance(o, dict):
        continue
    if str(o.get('mathdb_id', o.get('id'))) in want:
        o = {k: v for k, v in o.items() if k not in ('provenance', 'source_receipts', 'raw_line', 'statement_raw')}
        print(json.dumps(o, indent=1, ensure_ascii=False)[:mx])
        print('=====')
