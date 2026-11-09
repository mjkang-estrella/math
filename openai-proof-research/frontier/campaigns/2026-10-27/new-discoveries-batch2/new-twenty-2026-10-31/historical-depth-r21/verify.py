from pathlib import Path
import json,hashlib,resource
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(45,45))
O=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();R=json.loads((O/'reservation.json').read_text());results=json.loads((O/'results.json').read_text());raw=json.loads((O/'raw-bindings.json').read_text());old=json.loads((O/'old-dispositions.json').read_text())
assert len(results)==40 and set(results)==set(map(str,R['ids']))
for path,h in R['prior_report_hashes'].items():assert H(Path(path).read_bytes())==h
chunks={}
for i,x in results.items():
 assert x['old_disposition']==old[i]['disposition'] and x['old_reason']==old[i]['reason'];assert x['accepted_credit']==0 and x['lean_endpoint'] is None
 r=raw[i];p=r['chunk']
 if p not in chunks:
  b=Path(p).read_bytes();assert H(b)==r['chunk_sha256'];chunks[p]=b.splitlines(keepends=True)
 line=chunks[p][r['line_one_based']-1];assert line==(O/'raw'/f'{i}.jsonl').read_bytes();assert H(line)==r['raw_sha256'];obj=json.loads(line);assert obj['mathdb_id']==int(i);assert obj['statement']==x['literal_statement'];assert H(obj['statement'].encode())==r['statement_sha256']
 for s in x['new_source_hashes']:assert H((O/s['path']).read_bytes())==s['sha256']
for name in ['receipts.json','receipts-second.json','receipts-third.json']:
 for r in json.loads((O/'sources'/name).read_text()):
  if 'file' in r:assert H((O/'sources'/r['file']).read_bytes())==r['sha256']
screen=json.loads((O/'sources/registry-screen.json').read_text());tree=Path(screen['reused_tree']);assert H(tree.read_bytes())==screen['sha256'];t=json.loads(tree.read_text());assert t['sha']==screen['tree_sha'] and not t['truncated'];assert json.loads((O/'sources/registry-head.json').read_text())['sha']==screen['live_head']
assert sum(x['new_primary_body_review'] for x in results.values())==4
if (O/'manifest.json').exists():
 for r in json.loads((O/'manifest.json').read_text()):assert H((O/r['path']).read_bytes())==r['sha256'],r['path']
print(json.dumps({'status':'PASS','id_keys':40,'prior_reports':2,'new_primary_body_ids':4,'new_credit':0,'raw_lines_and_source_bytes':'verified','ledger_context_mismatch':'recorded; not an immutable report mismatch'},indent=2))
