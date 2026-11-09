from pathlib import Path
import json,datetime
L=Path(__file__).resolve().parent
assert (L/'audit-receipt.json').is_file(), 'both exhaustive audits must pass first'
removed=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.pyc')):
  removed.append(str(p.relative_to(L)));p.unlink()
(L/'compiled-removal-receipt.json').write_text(json.dumps(dict(completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),count=len(removed),removed=removed,scope='own objects only, after source-identical fresh replay and both exhaustive audits'),indent=2)+'\n')
print('removed own compiled objects',len(removed))
