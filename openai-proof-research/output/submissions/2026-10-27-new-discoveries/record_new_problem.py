"""Persist a newly created, precisely scoped problem before posting its answer."""
import base64
import datetime
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
number = int(sys.argv[1])
event = json.loads(base64.b64decode(sys.argv[2]))
event['observed_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
match = re.search(r'/p/(\d+)', event['url'])
assert match
problem_id = int(match[1])
path = root / 'problem-connections.json'
data = json.loads(path.read_text())
paper = data['papers'][number - 1]
assert paper['number'] == number
if paper.get('created_problem') and paper['created_problem']['url'] != event['url']:
    raise RuntimeError('Refusing to replace an existing problem record')
paper['created_problem'] = event
paper['problem_ids'] = [problem_id]
paper['status'] = 'PROBLEM_CREATED_SOLUTION_PENDING'
tmp = path.with_suffix('.json.tmp')
tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
tmp.replace(path)
receipts = root / 'problem-connection-receipts'
receipts.mkdir(exist_ok=True)
(receipts / f'D{number:03}-new-problem.json').write_text(json.dumps(event, ensure_ascii=False, indent=2) + '\n')
print(f'D{number:03}: precise problem record created: {event["url"]}')
