from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent;B=L.parents[1];R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
governing=[]
for p in [R/'AGENTS.md',B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',B/'lanes/root-r156-handback/DECISION.md']:
 b=p.read_bytes();governing.append(dict(path=str(p),sha256=sha(b),bytes=len(b)))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
history=json.loads((L/'history-receipt.json').read_bytes())
# Deduplicate generated echoes only when a byte-identical original is in the inherited set.
groups={}
for p,h,z in history['records']:groups.setdefault(h,[]).append(p)
excluded=[]; originals=[]
for h,ps in groups.items():
 canonical=sorted(ps,key=lambda p:(any(x in p.split('/') for x in ['packet','consulted']),len(p.split('/')),p))[0]
 for p in ps:
  if p!=canonical and any(x in p.split('/') for x in ['packet','consulted']):excluded.append(dict(path=p,original=canonical,sha256=h))
  else:originals.append(p)
assert all(p in originals for p in history['original_r111_r113'])
save('history-qualification.json',dict(utc=utc,receipt_sha256=sha((L/'history-receipt.json').read_bytes()),original_body_count=len(originals),excluded_generated_echoes=excluded,original_r111_r113=history['original_r111_r113'],query_hits=[],qualification='All bodies queried, then exact byte-identical generated role echoes removed. No entire lane excluded; no global cutoff. No worldwide semantic absence claim.'))
save('provenance.json',dict(utc=utc,lane=str(L),status='ZERO_NOMINEES',credit=0,baseline_counts={'additional':9,'total':39,'next':40},governing=governing,http=http,web_failures=[dict(url='https://www.mdpi.com/2227-7390/14/11/1797',status=429,channel='public web open',repeat=False)],web_searches=['graph conjecture 2026 irregular domination','Bastien Khormali link-irregular tournament conjecture','Refined Nordhaus Conjecture degree classes','2609.24707 proof conjecture','Strong Conjecture [F] irregular proof'],search_limits='Bounded public search; no absence clearance. Web tool search results are not archived full bodies.',guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=512*1024**2,group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,nominal_sampling_ms=40,limits='Sampling may miss short peaks; /proc visibility limits retained. No caps raised.'),registry_limits=['Fixed Omega490f and OpenAI7ef5 evidence retained via hashed inherited paths','Two capped300 comparisons not absence evidence','Current actual targeted tournament dossier/proof read; no complete current-head semantic sweep'],primary_science=['sources/induced.html','sources/induced-abs.html','sources/tournament-source.pdf','sources/tournament-proof.html','sources/companion.pdf'],no_completion_claim=True,no_lean_or_manuscript=True))
excluded_names={'finalmanifest.json','scientific-freeze.json','manifest-verification.json','checks-replay.log','finalize.log'}
files=[p for p in L.rglob('*') if p.is_file() and p.name not in excluded_names]
science=[p for p in files if not p.name.startswith('history-') and not p.name.startswith('context-')]
save('scientific-freeze.json',dict(utc=utc,entries={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(science)},status='Unresolved target, no universal source proof'))
files.append(L/'scientific-freeze.json')
save('finalmanifest.json',dict(utc=utc,entries={str(p.relative_to(L)):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted(files)},exclusions=sorted(excluded_names-{'scientific-freeze.json'}),scope='All lane payload files, except self and mutable verification/run logs.'))
print('Frozen payload',len(files),'science',len(science),'qualified originals',len(originals),'generated echoes removed',len(excluded))
