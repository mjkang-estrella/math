import pathlib,json,hashlib,collections,datetime
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();res=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(res)==20 and set(res)==set(map(str,ids));assert all(x['credit']==0 and x['lean_endpoint'] is None for x in res.values())
for i,x in res.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n') and sha(b)==x['provenance']['raw_sha256'];assert sha(x['statement'].encode())==x['provenance']['statement_utf8_sha256']
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text());b=p.with_name(p.name.removesuffix('.receipt.json'))
 if r.get('sha256'):assert b.exists() and sha(b.read_bytes())==r['sha256'],p
for p in [D/'SUMMARY.md',D/'CANDIDATE.md']:assert p.stat().st_size>100
# Ensure compact log actually contains all required N,k combinations.
coverage=set()
for name in ['compact-22-24-k3','compact-22-24-rest']:
 import re,math
 ls=(D/f'logs/{name}.log').read_text().splitlines()
 for a,b in zip(ls[::2],ls[1::2]):
  n,k=map(int,re.search(r'N (\d+) k (\d+)',a).groups());coverage.add((n,k));assert b.startswith('unimodal 1 sum ');assert int(b.split()[-1])==math.factorial(n)
assert all((n,k) in coverage for n in range(22,25) for k in range(3,n+1))
a=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),records=20,proposed_new_solutions=0,raw_statement_hashes='pass',retained_http_body_hashes='pass',compact_coverage='pass',lean_packet=None,limitations='Bounded research handback; no global novelty clearance or full assignment-depth claim.');(D/'final-audit.json').write_text(json.dumps(a,indent=2)+'\n')
manifest={str(p.relative_to(D)):dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(D.rglob('*')) if p.is_file() and p.name!='artifact-manifest.json'};(D/'artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(a));print('manifest files',len(manifest))
