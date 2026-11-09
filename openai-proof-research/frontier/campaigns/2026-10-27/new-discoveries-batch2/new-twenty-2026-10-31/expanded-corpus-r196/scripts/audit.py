import pathlib,json,hashlib,os
D=pathlib.Path(__file__).resolve().parents[1];h=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(r)==set(map(str,ids))
for i,x in r.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n') and h(b)==x['provenance']['raw_sha256'];assert h(x['statement'].encode())==x['provenance']['statement_utf8_sha256']
receipts=list((D/'sources').glob('*/receipt.json'))
for p in receipts:
 z=json.loads(p.read_text());b=p.with_name('body').read_bytes();assert h(b)==z['sha256'] and len(b)==z['bytes']
versions=json.loads((D/'outputs/versions.json').read_text());assert sum(len(x['versions_listed']) for x in versions.values())==35
# Current-running command groups matching our own numerical scripts, excluding this audit.
active=[]
for p in pathlib.Path('/proc').glob('[0-9]*/cmdline'):
 try:
  args=p.read_bytes().split(b'\0');name=str(D).encode()
  if int(p.parent.name)!=os.getpid() and any(name in a for a in args) and any(a.endswith(b'/limited.py') or a.endswith(b'/sandpile.py') or a.endswith(b'/eip.py') or a.endswith(b'/pebbling.py') for a in args):active.append(int(p.parent.name))
 except (OSError,ValueError):pass
assert not active,active
result={'id_count':len(r),'http_receipts_verified':len(receipts),'source_versions':35,'raw_lines_hash_verified':20,'active_numerical_processes':active,'lean_invocations':0,'accepted_credit':0,'scope':'local artifact integrity only; not mathematical certification'}
(D/'outputs/final-audit.json').write_text(json.dumps(result,indent=2));print(result)
manifest={str(p.relative_to(D)):h(p.read_bytes()) for p in D.rglob('*') if p.is_file() and p.name!='manifest.json'}
(D/'outputs/manifest.json').write_text(json.dumps(manifest,indent=2))
