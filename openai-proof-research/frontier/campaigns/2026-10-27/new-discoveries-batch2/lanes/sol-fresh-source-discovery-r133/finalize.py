import json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def row(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b))
def dump(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
inherited=[]
for rel in ['sol-fresh-source-discovery-r130/registry-delta-receipt.json','sol-fresh-source-discovery-r130/history-receipt.json','sol-renyi-registry-gap-closure-r3/semantic-read-receipts.json']:
 p=L.parent/rel
 if p.exists():
  b=p.read_bytes();inherited.append(dict(path=str(p),sha256=sha(b),bytes=len(b),qualification='Reused historical metadata, not semantic clearance of the r133 questions'))
shards=[json.loads((L/f'history-{i}.json').read_text()) for i in range(4)]
assert (L/'sources/burde-perfect.pdf').read_bytes()==(L/'sources/burde-perfect-retrieved.pdf').read_bytes()
dump('provenance.json',dict(lane=str(L),completed_utc=utc,status='UNRESOLVED_NO_NOMINEE',credit_requested=0,counts_inherited=dict(additional=9,total=39,next=40),sources=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()],context='context-receipts.json',historical_screen='history-receipt.json',matching_original_reopens='original-reopen-receipts.json',aliases='history-aliases.jsonl.gz',matching_aliases='matching-aliases.jsonl.gz',retained_original_science='retained-r111-r113-science.json',registry='registry-delta-receipt.json',inherited_receipts=inherited,guard=dict(path=str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),sha256=sha((L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py').read_bytes()),AS_bytes=512*1024**2,group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,BLAS_threads=1),omission_summary=[dict(shard=x['shard'],oversized=len(x['oversized']),role_paths=len(x['role_paths']),binary_paths=len(x['binary_paths']),errors=x['errors'],omitted_extensions=x['extensions_omitted']) for x in shards],limits=['Full lexical corpus is bounded by extension/12MB/role exclusions in each shard; semantic absence and worldwide priority are not certified.','Own lane excluded; historical corpus is not transactional.','Exact125-triple check is a classical nonperfect-g shortcut obstruction, not source resolution.','No full-source proof, no Lean or paper; no acceptance/count edits.'],failures_deviations=['Initial combined context native output truncated; bounded/structured replacement used.','Initial DOI fragment matched four large-integer substrings; preserved and removed by secondary digit boundary screen.','Web open author papers landing page returned inaccessible; not retried. Direct primary PDF had already succeeded.','Author PDF retrieved twice only to obtain structured HTTP receipt; exact equal bytes.','No registry Lean replay or full all-world source audit.'],external_mutations=False,git_operations=False,children=False))
core=[p for p in sorted(L.rglob('*')) if p.is_file() and (p.suffix in {'.md','.py','.sh'} or p.parent.name=='sources') and not p.name.startswith('context-')]
dump('scientific-freeze.json',dict(utc=utc,files=[row(p) for p in core],mutable_context_excluded=True,note='Not an acceptance. Historical scans/HTTP/provenance separately bound by finalmanifest; frozen math excludes mutable NEXT/ledger context copies.'))
print('science freeze',len(core),'inherited receipts',len(inherited))
