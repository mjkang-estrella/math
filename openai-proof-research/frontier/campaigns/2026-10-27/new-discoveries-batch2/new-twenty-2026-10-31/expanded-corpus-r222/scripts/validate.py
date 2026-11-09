import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'reservation.json').read_text());x=json.loads((D/'results.json').read_text());assert set(x)==set(map(str,r['ids'])) and len(x)==20
for i,o in x.items():
 b=(D/'raw'/(i+'.jsonl')).read_bytes();assert b.endswith(b'\n') and sha(b)==o['provenance']['raw_sha256'];q=json.loads(b);assert q['statement']==o['statement'] and sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert o['campaign_credit']==0 and o['lean_endpoint'] is None
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text());body=pathlib.Path(str(p)[:-13])
 if 'sha256' in o:assert body.exists() and sha(body.read_bytes())==o['sha256'],str(p)
for name in ['SUMMARY.md','CANDIDATE.md']:assert (D/name).stat().st_size>100
for name in ['isolation-n7','isolation-trees15-fixed','paths16','paths-random100-connectivity','threshold26']:
 assert json.loads((D/'logs'/(name+'.receipt.json')).read_text())['returncode']==0
 assert 'VIOLATION' not in (D/'logs'/(name+'.log')).read_text()
print(json.dumps({'exactly_20_ID_entries':True,'raw_statement_hashes':True,'HTTP_body_hashes':True,'outcomes':dict(collections.Counter(o['outcome'] for o in x.values())),'qualifying_endpoints':0},indent=2))
