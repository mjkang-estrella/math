from pathlib import Path
import json,hashlib,os,datetime
D=Path(__file__).resolve().parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();r=json.loads((D/'results.json').read_text());res=json.loads((D/'reservation.json').read_text())
assert set(r)==set(map(str,res['ids'])) and len(r)==20
for i,x in r.items():
 p=D/f'raw/{i}.jsonl';assert p.read_bytes().endswith(b'\n');assert sha(p)==x['provenance']['raw_sha256'];assert hashlib.sha256(x['statement'].encode()).hexdigest()==x['provenance']['statement_utf8_sha256']
 assert x['credit']==0 and not x['formal_endpoint_complete']
for p in (D/'sources').glob('*.receipt.json'):
 x=json.loads(p.read_text())
 if 'sha256' in x:
  f=Path(x['path']);assert sha(f)==x['sha256']
running=[]
for p in Path('/proc').glob('[0-9]*'):
 try:
  args=p.joinpath('cmdline').read_bytes().split(b'\0')
  if int(p.name)!=os.getpid() and args and b'python' in args[0] and any(str(D).encode() in a for a in args[1:]):running.append([int(p.name),[a.decode(errors='replace') for a in args if a]])
 except (OSError,ValueError):pass
assert not running,running
receipts={p.name:json.loads(p.read_text()) for p in (D/'logs').glob('*.receipt.json')}
report=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),entries=20,raw_and_statement_hashes_verified=True,source_receipt_hashes_verified=True,running_lane_python_jobs=running,resource_receipts=receipts,limitations='Canonical-tree classification and full Lean endpoint remain ordinary/unformalized; no accepted credit.')
(D/'outputs/final-audit.json').write_text(json.dumps(report,indent=2)+'\n')
manifest={str(p.relative_to(D)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in D.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}
(D/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');print('PASS: exactly20 IDs; source/raw hashes; no lane Python jobs. No Lean endpoint or accepted credit.')
