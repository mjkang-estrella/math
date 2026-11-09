"""Root documentary verification, adjudication and disjoint packet preparation."""
import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
resource.setrlimit(resource.RLIMIT_AS, (6*1024**3, 6*1024**3))
from pathlib import Path
import json, hashlib, datetime, collections, importlib.util
from urllib.parse import urlsplit, unquote
P = Path(__file__).resolve().parent.parent
ROOT = P/'root-intake-r60'
A = P/'virus-path-threshold-source-review-sol-r1'
def sha(q): return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q, value):
    assert not q.exists(), str(q)
    q.write_text(json.dumps(value, indent=2)+'\n')
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
assert json.loads((P/'ledger.json').read_text())['accepted_new'] == 57
ready0 = json.loads((ROOT/'virus-path-review-r1-ready.json').read_text())
assert sha(A/'TASK.txt') == ready0['task_sha256']
manifest = json.loads((A/'manifest.json').read_text())
entries = {x['path']: x for x in manifest['files']}
assert len(entries) == len(manifest['files']) == 116
for name, row in entries.items():
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    q = A/name
    assert not q.is_symlink() and sha(q) == row['sha256'] and q.stat().st_size == row['bytes'], name
exclusions = manifest['terminal_non_circular_exclusions']
assert set(exclusions) == {'manifest.json','seal-manifest.receipt.json','seal-manifest.output.txt'}
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()} == set(entries)|set(exclusions)
frozen = json.loads((A/'frozen-inputs.json').read_text())
assert len(frozen) == 25 and all(Path(n).is_relative_to(A) and sha(Path(n)) == h for n,h in frozen.items())
after = json.loads((A/'frozen-after.json').read_text())
assert after['count'] == 25 and after['mismatches'] == []
receipts = []
for q in sorted(A.glob('*.receipt.json')):
    row = json.loads(q.read_text())
    assert row['cwd'] == str(A) and row['cpu_limit_s'] == 115 and row['as_limit_bytes'] == 6*1024**3 and row['deadline_s'] == 130
    receipts.append(dict(path=q.name, sha256=sha(q), exit=row['exit']))
assert json.loads((A/'seal-manifest.receipt.json').read_text())['exit'] == 0
budget = json.loads((A/'search-budget.json').read_text())
assert budget == dict(calls_used=2, queries_used=6, maximum_calls=2, maximum_queries=6, charged_before_call=True)
charges = [json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()]
assert len(charges) == 2
previous = dict(calls_used=0, queries_used=0, maximum_calls=2, maximum_queries=6, charged_before_call=True)
for i, c in enumerate(charges, 1):
    assert c['sequence'] == i and c['before'] == previous and sha(A/c['plan']) == c['plan_sha256']
    assert json.loads((A/c['plan']).read_text())['queries'] == c['queries']
    expected = dict(previous)
    expected['calls_used'] += 1
    expected['queries_used'] += len(c['queries'])
    assert c['after'] == expected
    previous = expected
    assert json.loads((A/f'search-response-{i}.json').read_text())
assert previous == budget and sha(A/'charge_search.py') == sha(ROOT/'charge_search.py')
events = [json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()]
counts = collections.Counter(e['event'] for e in events)
assert counts == dict(attempt=3, success=2, unavailable=1)
for e in events:
    if e['event'] == 'success':
        assert sha(A/e['destination']) == e['sha256'] and (A/e['destination']).stat().st_size == e['bytes']
plans = [json.loads((A/n).read_text()) for n in ['get-plan-final.json','get-plan-prior.json','get-plan-original-final.json']]
assert {e['plan_sha256'] for e in events if e['event']=='attempt'} == {hashlib.sha256(json.dumps(plan,sort_keys=True).encode()).hexdigest() for plan in plans}
access = json.loads((A/'access-inventory.json').read_text())
assert access['protected_file_reads'] == access['protected_metadata_reads'] == access['author_lane_reads'] == []
review = json.loads((A/'review.json').read_text())
assert set(review) == {'322479'} and review['322479']['credit'] == 0 and review['322479']['campaign_count'] == 57
unavailable = json.loads((A/'new-unavailability.json').read_text())
assert len(unavailable) == 2
record = dict(utc=now, mathdb_id=322479, source_lane=str(A), task_genesis_verified=True,
    review_sha256=sha(A/'REVIEW.md'), proof_sha256=sha(A/'PROOF.md'), manifest_sha256=sha(A/'manifest.json'),
    verified_manifest_files=116, verified_frozen_bindings=25, runner_receipts=receipts,
    receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)), guard_events=dict(counts), search_budget=budget,
    search_counter_continuity='Both live before/after states, exact plan digests and query strings, full saved JSON responses and immutable helper verified.',
    root_disposition='EXCLUDE_COMPLETE_ROUTINE_ADAPTATION',
    ordinary='Independent all-coordinate P4 literal negation PASS retained. Actual cached 1111.0531v2 permits level4 and all branching integers1; map and threshold visually reviewed. Rational a1/2,b3/10 and weights(3,5,5,3) are the same single family as all-path/spectral variants.',
    prior='Actual Azizan Ruhi-Ahn-Hassibi1609.09565v1 Section2.2.1 p4 equations2.6 and2.9-2.12 were read. Reviewer supplies complete nonlinear-map identity delta=1-a,beta=b, all-initial-point global extinction and exact P4 spectral/parameter specialization. Distinct primary work, not recovery of denied WDWF2003. Root adopts documented routine adaptation exclusion; no claim the exact P4 refutation was previously printed.',
    significance='Explicit admissible counterexample to a later claimed theorem is the strongest contrary case; complete earlier general theorem-to-target reduction defeats significant-discovery credit under campaign rule. No exclusion based on shortness alone.',
    source='Cached2212.05733v2 Theorem4.1IIa conflicts with certificate in its displayed model. No claim unread 2026 journal final is false. Later final403; original journal delivery200 has only abstract/references, not full final theorem body. Final/correction fidelity remains HOLD independently of zero-credit decision.',
    family='Bounded trusted57+39 scope comparison reported nonoverlap; all P4/path/parameter/spectral variants one family.',
    process='One actual failed final-source GET preserved. Guard transport200 abstract-only delivery retained without rewriting success ledger; separate scientific body unavailability. No historical/protected path follow reported. Sampled/native/transient resource limits retained; no universal compliance claim.',
    root_scope='Documentary integrity and acceptance/routing adjudication only; no root mathematical solving/programs/Lean/checkers.',
    root_intake_repair='First verifier stopped before mutation: assumed guard plan digest was raw-file digest. Read immutable guard implementation; actual digest is canonical sorted-key JSON. Targeted verification corrected, worker files and guard ledger unchanged.',
    keyed_review=review, new_unavailability=unavailable, terminal_self_exclusions=exclusions,
    credit=0, accepted_new=57, target_new=60, formal_dispatch=False)
save(P/'virus-path-threshold-source-parent-integration-sol-r1.json',record)
den = json.loads((ROOT/'inherited-denials-r474.json').read_text())
den['utc'] = now
for index, plan in [(0,plans[0]),(1,plans[2])]:
    url = plan['url']
    key = urlsplit(url).hostname.lower()+unquote(urlsplit(url).path).rstrip('/')
    aliases = ['10.1080/00150517.2026.2711260','2212.05733'] if index==0 else ['1111.0531','viruslike dynamics on starlike graphs']
    den['blocked_keys'] = sorted(set(den['blocked_keys'])|{key})
    den['blocked_artifacts'] = sorted(set(den['blocked_artifacts'])|set(aliases))
    den['records'].append(dict(url=url,reason=dict(status=unavailable[index]['outcome'],artifact=unavailable[index]['work'],restriction='Entire identified work ALL NEW hosts, queries, versions, arXiv, author copies, caches, mirrors, DOI/API, body and metadata deliveries unavailable. No retry, alternate lookup or indirect recovery. Explicit pre-denial frozen original only is not final equivalence. Guard transport history unchanged.'),evidence=dict(path=str(A/'new-unavailability.json'),sha256=sha(A/'new-unavailability.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
steer = ('Completed322479 independent full ordinary P4 negation PASS, but ROOT EXCLUDE: actual Azizan Ruhi-Ahn-Hassibi1609.09565v1 Section2.2.1 equations2.6,2.9-2.12 supplies COMPLETE identical-map/global-extinction-to-P4 parameter/spectral bridge. Routine adaptation zero, not shortness or an exact earlier printed P4 refutation. Later cached2212.05733v2 actual Theorem4.1IIa conflict retained; unread final not declared false. Two NEW work-wide delivery restrictions: Takigawa-Miller final DOI10.1080/00150517.2026.2711260/source2212.05733 returned403; Becker et al Viruslike Dynamics on Starlike Graphs JNSA2013 pp53-63/source1111.0531 at jnsaonline.watsci.org/abstract_pdf/2013v4/v4n1-pdf/5.pdf returned200 two-page abstract/references only, not full final body. BOTH identified works ALL NEW alternate hosts/versions/arxiv/authors/caches/mirrors/DOI/API/body/metadata deliveries UNAVAILABLE; no retry/indirect recovery. Existing explicit frozen pre-denial originals only, no final equivalence. WDWF2003 block unchanged. Distinct1609.09565 not denied. Root verified116 own manifest files,25 frozen,3GET attempts/2transport successes/1HTTP403,2search6queries. No formal dispatch or credit;57/60 unchanged.')
den['root_virus322479_review_scope'] = steer
denpath = ROOT/'inherited-denials-r475.json'
save(denpath,den)
config = json.loads((ROOT/'r472-config.json').read_text())
config.update(number=473, protected_peers=['expanded-corpus-r472','lr-translation-degree-source-proof-review-sol-r1'],
    peer_routing_files=['selection-routing-r472.json','selection-routing-lr-degree-review-r1.json'],
    completed_discovery_numbers=sorted(set(config['completed_discovery_numbers'])|{471}),
    denials=str(denpath), steering=config['steering']+'\n'+steer+'\n', year_floor=2000,candidate_pool=400)
save(ROOT/'r473-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py')
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text())
forbidden=('formal','code-loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(token in part.lower() for token in forbidden) for name in allow for part in Path(name).relative_to(P).parts)
assert all('expanded-corpus-r463' not in name and 'expanded-corpus-r466' not in name for name in allow)
save(ROOT/'virus-review-new-denials-steering.json',dict(utc=now,message=steer,denials=str(denpath),immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(root_disposition=record['root_disposition'],manifest_files=116,frozen_bindings=25,receipt_exit_counts=record['receipt_exit_counts'],ready=ready)))
