"""Record a verified public problem link without creating duplicate claims."""
import base64
import datetime
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parent
number = int(sys.argv[1])
event = json.loads(base64.b64decode(sys.argv[2]))
event['observed_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
path = root / 'problem-connections.json'
plan = json.loads(path.read_text())
paper = next(x for x in plan['papers'] if x['number'] == number)
links = paper.setdefault('connections', [])
existing = next((x for x in links if x['problem_id'] == event['problem_id']), None)
if existing and existing.get('url') != event.get('url'):
    raise RuntimeError('Refusing to replace an existing verified problem connection')
if not existing:
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
