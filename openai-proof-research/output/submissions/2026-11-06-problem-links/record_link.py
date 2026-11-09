import datetime
import json
from pathlib import Path
import sys

base = Path(__file__).resolve().parent
identifier, observed_json = sys.argv[1:3]
observed = json.loads(observed_json)
path = base / 'prepared-links.json'
items = json.loads(path.read_text())
item = next(x for x in items if x['id'] == identifier)
assert any(a['href'].rstrip('/') == item['url'].rstrip('/') for a in observed['links'])
sections = [a['id'] for a in observed['ids'] if a['tag'] == 'SECTION' and a['id'].startswith('s')]
assert sections
item['solution_url'] = observed['url'].split('#')[0] + '#' + sections[-1]
item['status'] = 'posted_and_verified' if len(sys.argv) < 4 else sys.argv[3]
item['verified_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
(base / 'receipts').mkdir(exist_ok=True)
(base / 'receipts' / (identifier + '.json')).write_text(json.dumps(observed, indent=2) + '\n')
path.write_text(json.dumps(items, indent=2) + '\n')
print(json.dumps({'id': identifier, 'solution_url': item['solution_url'], 'status': item['status']}))
