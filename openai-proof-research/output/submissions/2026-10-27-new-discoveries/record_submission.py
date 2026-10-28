"""Persist observed submission events without replacing identifiers."""
import base64
import datetime
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parent
number = int(sys.argv[1])
event = json.loads(base64.b64decode(sys.argv[2]))
manifest_file = root / 'submission-manifest.json'
manifest = json.loads(manifest_file.read_text())
paper = next(p for p in manifest['papers'] if p['number'] == number)
metadata_file = Path(paper['metadata'])
metadata = json.loads(metadata_file.read_text())
for key in ('zenodo_draft_url', 'zenodo_url', 'doi', 'mathdb_url'):
    if event.get(key) and paper.get(key) and paper[key] != event[key]:
        raise RuntimeError(f'Refusing to replace {key}: {paper[key]}')
event['observed_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
for target in (paper, metadata):
    target.update({k: v for k, v in event.items() if k != 'evidence'})
if event.get('doi'):
    metadata['mathdb_comment'] = metadata['mathdb_comment'].replace(
        'PENDING_ZENODO_PUBLICATION', event['doi'])
manifest['status'] = 'SUBMISSION_IN_PROGRESS'
events_dir = root / paper['directory'] / 'submission-events'
events_dir.mkdir(exist_ok=True)
event_file = events_dir / (event['observed_at_utc'].replace(':', '-') + '.json')
event_file.write_text(json.dumps(event, ensure_ascii=False, indent=2) + '\n')
for path, data in ((metadata_file, metadata), (manifest_file, manifest)):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')
    tmp.replace(path)
print(f'Recorded D{number:03}: {event.get("publication_status")}')
