import pathlib,json,hashlib,datetime,re
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,x):(L/n).write_text(x if isinstance(x,str) else json.dumps(x,indent=2))
p=L/'discovery.md';s=p.read_text().replace('F_(w+2) copies of F1','F_(w+1) copies of F1').replace('one token F_(w+3)','one token F_(w+2)').replace('a token F_(w+2), immediately','a token F_(w+1), immediately');p.write_text(s)
# Stable administrative dispositions are snapshots, not immutable scientific originals.
bindings=[json.loads(x) for x in (L/'bindings.jsonl').read_text().splitlines()]
admin=[]
for row in bindings:
 p=pathlib.Path(row['path'])
 if p.parent.name.startswith('root-'):
  assert sha(p)==row['sha256']
  q=L/'administrative'/(p.parent.name+'--'+p.name);q.write_bytes(p.read_bytes());assert sha(q)==row['sha256'];admin.append({'original':str(p),'snapshot':str(q),'sha256':sha(q)})
save('administrative-dispositions.json',admin)
checks=json.loads((L/'exact-checks.json').read_text())
questions=json.loads((L/'question-bindings.json').read_text());proofs=json.loads((L/'proof-bindings.json').read_text())
access=json.loads((L/'primary-access.json').read_text())
provenance={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'research hold; no full endpoint','scope':'assigned lane only; solo; no shared/git/public/browser/MathDB edits; no Lean execution/manuscript','guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','limits':{'AS_bytes':512*1024*1024,'sampled_process_group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'raises':False},'scientific_inputs':{'question_bindings':'question-bindings.json','proof_bindings':'proof-bindings.json','search_inventory':'semantic-search-inventory.json','new_primary_access':'primary-access.json','focused_source':'access-zeckendorf.pdf.json','focused_current_history':'access-zeckendorf-current.html.json'},'administration':'administrative snapshots; not claimed immutable science','freeze_protocol':'Hash/size recorded before content reading; pre/post comparisons; existing immutable sources referenced in place without recursive copies. Fresh PDFs frozen before extraction; text hashed before scientific reads. Final external-reference verification separate from writes.','chronology':{'primary_zeckendorf_version':'v1, 20 October 2022; only v1 listed in current abstract-page history retrieved 30 October 2026','public_registry_commit':'unknown; cached counterpart content read but current HEAD and commit/publication date not certified','cache_directory_date':'not used as publication chronology','history_limits':'no exhaustive citing literature search or novelty clearance'},'search_scope':{'files':len(json.loads((L/'semantic-search-inventory.json').read_text())),'matching_files':len(json.loads((L/'semantic-search-hits.json').read_text())),'limits':'immediate report/problem bodies; not recursive archives or every imported proof dependency'},'checks':{'inputs':[2,18],'reachable_states':checks['states'],'arithmetic':'exact fractions','conclusion':'finite identity/method checks only; no CLT or uniform mixing conclusion'},'access_limits':['Author PDF TLS certificate failure; not bypassed','No retried denied GitHub/ScienceDirect/Google routes','Current public registry HEAD unavailable; novelty gate remains incomplete'],'final_manifest_excludes':['MANIFEST.json','verification-receipt.json']}
save('provenance.json',provenance)
save('SUMMARY.md','''# r279 handback

Screened twelve distinct attributed source-question families across finite structures, arithmetic, analysis and probability. Eleven have applicable cached public resolutions and are excluded before sustained solving. One incomplete research hold remains: Cheigh et al. Question6.5, uniform mixing for random Zeckendorf-game split indicators.

Sustained two routes. Empty digit bands alone fail as regeneration barriers; explicit arbitrary-width combine constructions explain why. The exact game-DAG length martingale gives a valid variance decomposition, verified on548 reachable states for inputs2–18; uniform concentration/Lindeberg estimates and the literal mixing endpoint remain unproved. The source's suggested polynomial-decay bridge also has exponent and event-union gaps. None is a discovery claim.

SCOUTING.md records exact scopes, source URLs, nearest proof bodies and objections. discovery.md gives the two mechanisms and missing quantifiers. provenance.json and source bindings record hashes/access/chronology limitations. Current public-registry HEAD is unknown; no novelty clearance is claimed. The twelve-family screen is biased toward cached resolutions, not twelve newly open problems.

Runnable capped checks: bash RUN.sh. Final manifest excludes itself and verification receipt; verify.py runs separately after writes. No PROOF.md, Lean execution, manuscript, shared/count edits, git, browser/public actions or children.
''')
save('progress.md','''# Final research status

Administrative snapshots and ancestor rules read. Twelve-family source/body screen completed before sustained mathematics. Concrete cached theorem statements and proof mechanisms exclude eleven families. Actual focused primary PDF and current arXiv history read; history lists only v1. Target is the exact all-N mixing question, with the informal CLT coefficient issue kept separate.

Two focused routes developed and stopped at explicit missing uniform lemmas. Exact rational checks pass for17 inputs/548 reachable states and eight spatial-gap counterexamples. These are finite diagnostics and helper identities only. No ordinary full endpoint proved/refuted and no qualified nomination. Final evidence written; separate guarded verification is the final operation.
''')
save('FAILURES.md','''# Preserved failures and limits

1. Initial unrestricted recursive rg --files capture raised MemoryError under the prescribed512MiB AS cap. No cap increase. Bounded two-level inventory replaced it; failures/inventory-memory.txt preserves the failure and the tool transcript has the traceback. Avoid repeating broad inventories.
2. Tărnăuceanu author PDF failed SSL certificate verification. The exact error remains in primary-access.json. No disabled TLS, alternate challenge route or proxy. Original-body gap retained.
3. Several large tool outputs were truncated. Follow-up compact/endpoints reads supplied the exact target and settling declarations; no unshown full dependency audit is claimed.
4. Generic empty-bin regeneration is false; arbitrary-width deterministic constructions preserved in discovery.md and exact-checks.json. Their path probabilities were not uniformly bounded, so this does not refute mixing.
5. Martingale quadratic variation concentration and conditional Lindeberg are missing. Finite moment identities do not imply either, nor the literal strong-mixing statement.
6. Source Question6.6's decay exponent2+epsilon does not alone yield the weighted summability of Question6.5; cylinder events do not automatically control arbitrary event unions. These are method objections, not a new game counterexample.
7. Current registry head and exact public proof publication chronology are unknown. Cache folder dates do not supply either. No denied endpoint was retried; historical access gaps remain parked. No worldwide-priority, all-citer or specialist-database coverage claim.
''')
save('RUN.sh','''#!/bin/sh
set -eu
LANE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
exec python "$LANE/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python "$LANE/checks.py"
''')
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
save('MANIFEST.json',manifest)
print('finalized',len(manifest),'payload files; verification must be separate')
