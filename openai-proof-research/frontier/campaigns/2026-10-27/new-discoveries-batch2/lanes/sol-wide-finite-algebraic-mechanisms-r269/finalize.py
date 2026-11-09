import pathlib,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
root=L.parents[5]
# Administrative files are snapshots, never scientific frozen inputs.
p=root/'AGENTS.md'
if p.exists():(L/'admin'/'ancestor-AGENTS.md').write_bytes(p.read_bytes())
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
prov=dict(lane=str(L),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),guard=str(guard),guard_sha256=sha(guard),caps=dict(AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230),threads=1,bytecode=False,scientific_inputs=['bindings.json','derived.jsonl','access.jsonl','history-bindings.json'],administrative_snapshots_only=True,registry_head='unknown; inherited denied routes parked',counts=dict(additional=9,total=39,next=40,authority='root only'),credit_requested=0)
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
post=[]
for r in json.loads((L/'bindings.json').read_text()):
 assert sha(pathlib.Path(r['original']))==r['sha256']==sha(pathlib.Path(r['copy']));post.append(r['original'])
for r in map(json.loads,(L/'derived.jsonl').read_text().splitlines()):
 assert sha(pathlib.Path(r['source']))==r['sha256'];assert sha(pathlib.Path(r['text']))==r['text_sha256']
(L/'source-postcheck.json').write_text(json.dumps(dict(status='PASS',frozen_reports=post,primary_bindings_verified=19),indent=2)+'\n')
files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
(L/'final-manifest.json').write_text(json.dumps(files,indent=2)+'\n');print('manifest files',len(files))
