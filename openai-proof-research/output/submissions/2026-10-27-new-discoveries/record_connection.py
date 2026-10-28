"""Record a verified public problem link without creating duplicate claims."""
import base64
import datetime
import json
from pathlib import Path
import sys
from urllib.parse import urlsplit

root = Path(__file__).resolve().parent
number = int(sys.argv[1])
event = json.loads(base64.b64decode(sys.argv[2]))
event['observed_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
path = root / 'problem-connections.json'
plan = json.loads(path.read_text())
paper = next(x for x in plan['papers'] if x['number'] == number)
links = paper.setdefault('connections', [])
existing = next((x for x in links if x['problem_id'] == event['problem_id']), None)
if existing:
    old, new = urlsplit(existing['url']), urlsplit(event['url'])
    if old.fragment != new.fragment or old.path.split('/')[2] != new.path.split('/')[2]:
        raise RuntimeError('Refusing to replace an existing verified problem connection')
    event['verified_page_url'] = event['url']
    event['url'] = existing['url']
    event['previous_label'] = existing.get('label')
    existing.update(event)
else:
    links.append(event)
paper['status'] = event.get('status', 'CONNECTED')
tmp = path.with_suffix('.json.tmp')
tmp.write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
tmp.replace(path)
receipts = root / 'problem-connection-receipts'
receipts.mkdir(exist_ok=True)
receipt = receipts / f'D{number:03}-{event["problem_id"]}.json'
receipt.write_text(json.dumps(event, ensure_ascii=False, indent=2) + '\n')
print(f'D{number:03}: {event.get("kind")} -> {event["url"]}')
