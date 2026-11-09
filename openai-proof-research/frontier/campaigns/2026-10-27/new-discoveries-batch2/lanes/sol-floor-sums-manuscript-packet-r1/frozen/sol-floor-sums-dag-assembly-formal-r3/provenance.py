from pathlib import Path
import json,hashlib,datetime,collections
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
inv=json.loads((L/'assembly-inventory.json').read_text());assert len(inv)==12459
counts=collections.Counter(d['rule'] for d in inv)
mods=json.loads((L/'checked-modules.json').read_text())
r=dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 status='unconditional literal endpoint compiled; audit/replay receipts separate',
 endpoint='Assembly.literal_endpoint : FloorSums.LiteralEndpoint',
 sorted_endpoint='Assembly.sorted_clamped_bound : FloorSums.SortedClampedBound',
 root='Assembly.n22671 (v : Assembly.Vars) (q : Assembly.Query v) : Assembly.e7489 v',
 original_integer_fields=['m','H','t','a','b','c','d'],free_fresh_fields=[],
 source_DAG_nodes=22672,reachable_rule_nodes=12459,rule_counts=dict(counts),
 query_assertions=18,query_used_assertions=17,fresh_actual_definitions=128,
 hypothesis_discharge_rules=644,root_residual_hypotheses=inv[-1]['hyps'],
 inherited_arithmetic_implications=1329,inherited_literal_source_declarations=59,
 modules=mods,proof_source_hashes={m:sha(L/(m.replace('.','/')+'.lean')) for m in mods},
 original_audit=json.loads((L/'original-audit-receipt.json').read_text()),
 scientific_freeze='freeze.json',source_pin='frozen/protocol/upstream.json',
 resource_protocol='RUN.md',failures='FAILURES.md',
 primary_source_scope='Thanatipanonda–Wong 2018 §4 pp14–15, four-variable lower bound; not all of later Conjecture17',
 prior_art_access='Inherited bounded actual-body evidence only; no new retrieval, no current registry clearance; old inaccessible intervals parked',
 chronology='Original primary 2018 conjecture and 2017 predecessor; inherited October30 2026 computational proof/review; source chronology/provenance retained in frozen direct packets',
 novelty='HOLD',acceptance='HOLD',counts='9 additional /39 total /next40; root alone accepts')
assert not r['root_residual_hypotheses'] and counts['lemma']==644
(L/'provenance.json').write_text(json.dumps(r,indent=2)+'\n');print('source closure provenance',len(mods),'modules')
