import os, resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
resource.setrlimit(resource.RLIMIT_AS, (6*1024**3, 6*1024**3))
from pathlib import Path
import json, hashlib, datetime, collections, shutil
P = Path(__file__).resolve().parent.parent
ROOT = P/'root-intake-r60'
R = P/'cmdrr-five-three-formal-sol-r4'
O = P/'cmdrr-five-three-source-review-sol-r1'
L = P/'cmdrr-five-three-formal-independent-review-sol-r5'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p, d):
    assert not p.exists(), str(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(d, indent=2)+'\n')
assert not L.exists()
assert json.loads((P/'ledger.json').read_text())['accepted_new'] == 55
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
m = json.loads((R/'SHA256-MANIFEST.json').read_text())
files = m['sha256']
assert len(files) == m['file_count'] == 739
assert all(not Path(n).is_absolute() and (R/n).resolve().is_relative_to(R) for n in files)
assert all(sha(R/n) == v for n,v in files.items())
frozen = json.loads((R/'frozen-inputs.json').read_text())
for n,v in frozen.items():
    assert 'shoe-pair-discrepancy-formal-sol-r4' not in n and 'expanded-corpus-r437' not in n
    assert sha(Path(n)) == v
after = json.loads((R/'frozen-after.json').read_text())
assert len(frozen) == after['count'] == 707 and not after['mismatches']
state = json.loads((R/'results/326555.json').read_text())
replay = json.loads((R/'results/REPLAY-R4.json').read_text())
order = replay['order']
assert len(order) == len(set(order)) == len(state['modules']) == 39 and replay['empty_build_verified']
assert replay['sources_before'] == replay['sources_after_checkers']
assert replay['lean_path'].split(':')[0] == str(R/'extracted-r4/build')
assert all('/2026-10-14/formal/.lake/packages/' in s for s in replay['lean_path'].split(':')[1:])
receipts = []; by_label = {}
receipt_names = [n for n in files if n.startswith('receipt/') and n.endswith('.json')]
receipt_names += [n for n in m['exact_terminal_noncircular_self_exclusions'] if n.startswith('receipt/')]
for n in receipt_names:
    j = json.loads((R/n).read_text())
    assert Path(j['log']).resolve().is_relative_to(R) and sha(Path(j['log'])) == j['log_sha256']
    assert j['group_members_left'] == []
    row = dict(path=n, sha256=sha(R/n), label=j['label'], exit=j['exit'], stamp=j['stamp'],
               guard=j.get('guard'), group_members_left=j['group_members_left'])
    receipts.append(row)
    if j['label'] not in by_label or j['stamp'] > by_label[j['label']]['stamp']:
        by_label[j['label']] = row
for modrow in state['modules']:
    mod = modrow['module']
    s = sha(R/'src'/f'{mod}.lean')
    assert s == modrow['source_sha256'] == replay['sources_before'][mod]
    assert sha(R/'extracted-r4/src'/f'{mod}.lean') == s
    assert sha(R/'build'/f'{mod}.olean') == modrow['working_olean_sha256']
    assert sha(R/'extracted-r4/build'/f'{mod}.olean') == modrow['replay_olean_sha256'] == replay['oleans_after_checkers'][mod]
    ownrec = json.loads((R/modrow['latest_strict_receipt']).read_text())
    assert ownrec['exit'] == 0 and ownrec['source_sha256'] == s
    for lab in ['lean_'+mod, 'replay_strict_'+mod, 'replay_checker_'+mod]:
        assert by_label[lab]['exit'] == 0, lab
        j = json.loads((R/by_label[lab]['path']).read_text())
        if 'strict_' in lab or lab.startswith('lean_'):
            assert '-j1' in j['argv'] and '-M3500' in j['argv'] and '-DwarningAsError=true' in j['argv']
assert state['mathematical_unpaid_lemmas'] == [] and state['credit'] == 0
parent = P/'cmdrr-five-three-formal-parent-integration-sol-r4.json'
save(parent, dict(utc=now, mathdb_id=326555, source_lane=str(R), manifest_sha256=sha(R/'SHA256-MANIFEST.json'),
    manifest_files_verified=len(files), manifest_mismatches=[], frozen_verified=len(frozen), frozen_mismatches=[],
    frozen_after=after, receipt_count=len(receipts), receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),
    receipts=receipts, source_only_module_order=order, latest_receipts=by_label,
    replay_scope='39 source/proof/control/audit modules, working and empty-build extracted sources/oleans rehashed; latest strict/checker receipts all zero',
    author_audit=state['audit'], author_visual_qa=state['visual_qa'], controls=state['controls'],
    retained_process_limits=state['process_limits'], prior_limits=state['prior_limits'],
    historical_breach='r3 workspace-root recursive metadata traversal and missing interrupted-run receipt/reap evidence remain unresolved/unaccepted. No protected proof-body bytes reported read. Later frozen passes or clean replay do not retroactively waive it.',
    root_status='FULL_ENDPOINT_RECEIPTS_VERIFIED__INDEPENDENT_FINAL_REVIEW_UNPAID',
    root_scope='Documentary hash/receipt/orchestration only, no mathematical/compiler/checker execution or independent body/source/visual verification',
    independent_review_required=['literal original/final source translation', 'all new proof bodies and exact endpoint chain', 'fresh strict builds and kernel checks', 'full production/private/generated reachable body/type DAG and endpoint closures', 'source/semantic controls', 'six-page paper and reporting', 'process/provenance significance adjudication'],
    credit=0, accepted_new=55, target_new=60, previous_accepted=39))

L.mkdir(); origins = {}
def cp(src, rel):
    dst = L/rel; dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    assert sha(src) == sha(dst)
    origins[rel] = dict(path=str(src), sha256=sha(src))
for n in ['bootstrap.py','runner.py','write_lane.py','verify_frozen.py','check.sh','checker.sh','PINS.json']:
    cp(R/n, n)
assert 'os.chdir(lane)' in (L/'runner.py').read_text()
for n in ['src','build','audit','receipt','logs','tmp','cache','results','output/pdf']:
    (L/n).mkdir(parents=True, exist_ok=True)
pins = json.loads((L/'PINS.json').read_text())
assert sha(Path(pins['lean_bin'])) == pins['lean_sha256']
assert sha(Path(pins['leanchecker_bin'])) == pins['leanchecker_sha256']
upstream = [str(Path(pins['packages_root'])/n/'.lake/build/lib/lean') for n in ['mathlib','batteries','aesop','Qq','proofwidgets','importGraph','LeanSearchClient','plausible']]
(L/'env.sh').write_text('#!/bin/bash\nset -eu\nLANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)\nLEAN_BIN='+str(Path(pins['lean_bin']).parent)+'\nexport PATH="$LEAN_BIN:$PATH"\nexport LEAN_PATH="$LANE/build:'+':'.join(upstream)+'"\n')
# Prospective, named own-log display exception, separately capped and recorded.
display = (R/'display_log.py').read_text().replace(str(R), str(L))
(L/'display_log.py').write_text(display)
for mod in order:
    cp(R/'src'/f'{mod}.lean', f'inputs/author-src/{mod}.lean')
    cp(R/'src'/f'{mod}.lean', f'src/{mod}.lean')
for n in ['SUMMARY.md','CHECKPOINT.md','SHA256-MANIFEST.json','frozen-before.json','frozen-after.json','frozen-inputs.json','PINS.json','TASK.txt','INPUT-ORIGINS.json','RUNNER-DELTA.json','SOURCE-BASELINE-ORDER.json','replay.py','audit_summary.py','finalize.py','seal.py','results/326555.json','results/REPLAY-R4.json','results/SOURCE-DEFINITION-MAP.json','audit/FINAL-AUDIT-SUMMARY.json','audit/ENDPOINT-CLOSURES.json','audit/PROCESS-INVENTORY.json','audit/COMPLETED-RECEIPT-INVENTORY.json','audit/VISUAL-QA.json','manuscript/PAPER.md','manuscript/PAPER.roff','output/pdf/cmdrr-five-three.pdf']:
    cp(R/n, 'inputs/author/'+n)
for row in receipts:
    n = row['path']; cp(R/n, 'inputs/author/'+n)
    j = json.loads((R/n).read_text()); rel = str(Path(j['log']).relative_to(R))
    cp(R/rel, 'inputs/author/'+rel)
for q in (R/'controls-negative').rglob('*'):
    if q.is_file() and q.suffix in ['.lean','.json','.py','.sh']:
        cp(q, 'inputs/author-controls/'+str(q.relative_to(R/'controls-negative')))
for n in ['REVIEW.md','INDEPENDENT-PROOF.md','DORMANT-OBLIGATIONS.md','keyedreview.json','ACCESS-SEARCH-READ-INVENTORY.json','RESOURCE-INVENTORY.json','SHA256-MANIFEST.json','guard-ledger.jsonl']:
    cp(O/n, 'inputs/ordinary-review/'+n)
for n in ['literal326555.jsonl','literal-provenance.json','original-twenty.jsonl','FULLCANDIDATE.md','DORMANT-SOL-FORMAL-PLAN.md','registry-and-pinned-inventory.json','prior-reconciliation.json','accepted55-routing.json','prior39-routing.json','sources/design.pdf','sources/design.txt','sources/design-final.pdf','sources/design-final.txt','sources/design-final-landing.html']:
    cp(O/'inputs'/n, 'inputs/source/'+n)
for n in ['cmdrr-r4-log-display-exception.json','cmdrr-r4-pdf-marker-path-resolution.json','inherited-denials-r437.json']:
    cp(ROOT/n, 'inputs/root/'+n)
cp(P/'cmdrr-five-three-formal-parent-integration-sol-r3.json','inputs/root/HISTORICAL-R3-INTEGRATION.json')
cp(parent, 'inputs/root/AUTHOR-R4-INTEGRATION.json')
save(L/'SOURCE-ORDER.json', order)
save(L/'INPUT-ORIGINS.json', origins)
save(L/'ROOT-PREP.json', dict(utc=now, role='Independent final adversarial review', mathdb_id=326555,
    model='gpt-6.1-sol', reasoning='high', service='default', children=False,
    active_protected=['shoe-pair-discrepancy-formal-sol-r4','expanded-corpus-r437'],
    author_integrity_record=str(parent), network=False, credit=0, campaign=55, previous=39,
    source_scope='Own copied source and author evidence only; upstream API read-only; no author oleans or legacy build paths',
    generic_helpers='Copied current r4 runner already has own-cwd guard; caps/reap unchanged; separate own-log display helper prospectively authorized'))
task = '''INDEPENDENT FINAL REVIEW, MathDB326555 CMDRR(5,3), GPT-6.1 Sol high/default personally ONLY; no children or fallback. Current55/60 beyond39prior. Root orchestrates, does no mathematics/compiler execution. This is a NEW independent review, not author continuation or self-acceptance. Work only OWN_LANE; no git/network/search/HTTP/browser/account/messages/installs/shared/parent/author writes, no external /tmp or background jobs. Other lanes, especially shoe-pair-discrepancy-formal-sol-r4 and expanded-corpus-r437, protected: never read/hash/glob/list/stat/poll. Exact copied-input provenance paths may ONLY be hashed by mandatory verifier; embedded paths are NOT permission to research-read them.

FIRST command EXACTLY `timeout 20 python3 -I -B OWN_LANE/bootstrap.py`, with exec workdir OWN_LANE. Read printed full TASK and AGENTS chain, preserve receipt. SECOND command `timeout 140 python3 -I -B OWN_LANE/verify_frozen.py before`, workdir OWN_LANE. No prior math/source/API inspection. Every later substantive source/API/audit/compiler/render read or operation via immutable OWN runner; every exec sets explicit OWN_LANE workdir. `source OWN_LANE/env.sh; timeout 140 python3 -I -B OWN_LANE/runner.py UNIQUE_LABEL -- COMMAND ARGS`. Wrappers source environment: **bash** OWN_LANE/check.sh MODULE, **bash** OWN_LANE/checker.sh MODULE (not path-form leanchecker, no permission126). No runner --help, recursive workspace inventory, tty/proc-fd/catchall traversal, overlapping jobs or unbound shell vars. Runner forces own cwd before child dispatch. Only own build + pinned upstream read-only oleans, no author/legacy oleans. PINS/helpers/frozen inputs immutable; extraction plans use DIFFERENT filenames. Caps2cores CPU120 AS12GiB sampled-groupRSS6GiB devguard130/wall140 arena2; strict Lean4.34.1 -j1 -M3500 -DwarningAsError=true. Full true-exit logs/receipts every attempt, no tail pipeline masking, no unchanged failed reruns, all groups reaped. Do not describe sampled limits as cgroup guarantees.

Prospective OWN-LOG DISPLAY exception: `timeout 20 python3 -I -B OWN_LANE/display_log.py ABSOLUTE_OWN_LOG_PATH OFFSET [EXPECTED_SHA256]` displays max16384 bytes and records audit/displays JSON. It front-caps affinity2/CPU10/AS512MiB before reading. Known own saved runner logs only, no recursive enumeration/following embedded paths. This is standalone documentary display, no sampled-group/native-UI telemetry, NOT compiler-runner execution. Source/API reads remain runner-mediated. For author copied logs, read via runner to create an own log then display own log. Direct view_image of own rendered documentary pages allowed as distinct UI evidence with candid telemetry limits. All new text via write_lane.py RELPATH TEXT stdin; no binary/base64/empty Lean payload. Binary images/render outputs only through documented capped generator.

Read inputs/source exact literal/provenance/original20, original preprint and FINAL scanned journal source (Definition1.2, Conjecture2.4, applicable general spectrum/context). Failed OCR text is not body evidence; render and visually inspect necessary final source pages. Read ordinary independent review/proof, root r3/r4 integrations, retained denial/access/registry/accepted55+prior39 scope evidence. No old accepted certificate audits; trusted scope comparisons only. Specific 2013 Berman-Smith companion remains403-unread across ALL alternate delivery; no network/retry/claim of global novelty. Distinguish generic bounded unknown from a specific applicable unread theorem. Review significance independently: complete prior-result bridge required for routine exclusion, include strongest contrary argument; small size, standard permutation signs, easy formalization alone do NOT establish routine. Record chronology/current-registry evidence limits candidly; do not turn source summaries into proof-body clearance.

AUTHOR CLAIM to independently test: all actual source-model CMDRR(5,3) schedules impossible, including arbitrary five-element male/female types and arbitrary matching of THREE spouse pairs. Literal ambiguous k gloss is source-bound to spouse pairs per Def1.2, NOT number of rounds/games. 39 source/proof/control/audit modules, order SOURCE-ORDER.json, copied byte-identically into own src and immutable inputs/author-src. Empty own build must be VERIFIED, then strict compile and kernel-check ALL39 from own sources with upstream-only LEAN_PATH. Verify binary and actual package-pin metadata BEFORE first compiler call. Fresh independent source-only replay with source hashes equal author copies and post-checker olean/source rehash; no author olean import. Classify mathematical modules vs auxiliary audit/controls honestly. Perform actual independent full source-to-Lean and proof-body review, not just compiler success. Check Source models arbitrary finite game occurrences, spouses never together, exact partner/opponent multiplicities, same-sex single repeat semantics, no extra round/resolvability/Latin/simplicity/normalization hypotheses or answer-bearing fields. Follow occurrence/cell bijections, all arbitrary-source normalization/transport bridges into final chain. Check actual A=0, A+B=1+z, B+z=2, row and COLUMN cycle classification/correspondence, universal single-cycle elimination, permutation U/C/T sign contradiction, and canonical_noSource -> noSource_five_three -> universalExistsFiveThree_negation. Verify every unpaid mathematical bridge is paid and source-faithful rather than an unconsumed idle theorem or assumed identity. Source completeness must justify existential/universal sequence/type encoding, not only a fixed matrix instance.

Independently deep-audit actual production-origin declarations INCLUDING private/generated, all reachable body/type dependencies and exact per-endpoint closures. Enumerate whole environment origins, but do not serialize unrelated imported bodies needlessly. No opaque/unsafe/partial/extern/implementedBy/native_decide/new axioms/sorry/admit. Only propext Classical.choice Quot.sound permitted; #print axioms alone is NOT full body-origin audit. Verify production classification, DAG edges/visited union/closure counts and exact source-link consumption. Reproduce/review audit code rather than trusting counts. Author reports271358 environment constants,444 production declarations,9733 union body nodes; exact universal closure9562. Independently count and report corrections if needed. Audit also controls/aux roots separately and distinguish kernel-reducible opaque bodies from unsupported primitives precisely.

Review and rerun meaningful source-positive/nonvacuity controls and isolated semantic-mutation negatives; expected-fail process exit must be real and caused by intended source/claim mismatch, not broken import/environment. Author controls include unchanged positive source and changed repeat/partner multiplicities. Preserve exact source changes/logs and original-contaminated failed attempts. Do not mistake negative demonstration failure for proof of an unrelated stronger theorem. No mathematical Python/numerical enumeration/CAS/solver; mathematical reasoning and Lean only, documentary scripts allowed.

Read ALL six pages of inputs/author/output/pdf/cmdrr-five-three.pdf, render independently under own runner and actually view EVERY page; use installed PDF SKILL read via runner, announce usage. This is read-only PDF review; no authoring marker required. Check every theorem/hypothesis, literal translation, ordinary proof including column correspondence, source theorem citations, exact axiom/DAG/replay/control counts, claimed scope, 55/60 status and pending credit, source-prior caveats and process statements. Do NOT edit author/PDF; report precise page/line errata with concrete suggested prose. No new PDF required. Avoid copying author 'visual QA' as independent inspection.

PROCESS separate from mathematical/formal PASS: historical r3 initial inventory omitted cwd, recursively traversed workspace-root metadata; protected-peer metadata traversal cannot be excluded, no protected proof-body bytes reported read. Interrupted run has no normal receipt/reap evidence; later completed empty groups/frozen passes/source-only replay DO NOT retroactively clear that breach. Root permitted continuation with NEW cwd guard, not waiver. r4 direct helper read outside capped runner, actual package pin read after initial baseline compile (before final replay), standalone prospective display exception, wrong-path failed PDF marker then one corrected successful absolute marker, PDF rendering/report/audit-summary corrections and native display telemetry limits remain retained. Read full copied PROCESS-INVENTORY, receipt/log inventory and root log/PDF decisions. Assess whether current replay and independent checks give reliable technical provenance despite history; identify material unresolved contamination/evidence risks explicitly without inventing protected access or asserting historic cleanup. Root alone adjudicates process acceptance; never label universal compliance PASS. No retroactive receipt/ledger repair. If a serious new own breach occurs stop affected activity, preserve evidence and report it, do not silently restore/relabel as compliance.

Deliver FINAL-REVIEW.md, ID-keyed review.json with SEPARATE ordinary correctness / literal+final source / proof-body / fresh strict+checker+replay / full transitive origin audit / controls / manuscript / prior-novelty-significance / historical/current process / overall recommendation gates; exact source map, specific objections and strongest contrary arguments, reproducible fresh receipt/hash inventories, source comparison and all-page QA. Technical PASS is not acceptance; recommend accept/revise/exclude with reasons, retain old access/process limits. If a repair is needed report exact minimal fix, no rewriting production proof to make review pass. Continue all authorized independent work until full review done. Root credit unchanged0/current55/60, no ledger edits/self-acceptance. Finish mandatory verify_frozen after, no later frozen writes, manifest actual all sources/helpers/pins/plans/copied-inputs/receipts/logs/audit/replay/render/reports with exact terminal noncircular self-exclusions and post-checker hashes. Handback actual disk state and exact unpaid obligations, all jobs reaped.
'''.replace('OWN_LANE', str(L))
(L/'TASK.txt').write_text(task)
bindings = {str(R/n): v for n,v in files.items()}
bindings.update(frozen)
bindings[str(R/'SHA256-MANIFEST.json')] = sha(R/'SHA256-MANIFEST.json')
for n in m['exact_terminal_noncircular_self_exclusions']:
    bindings[str(R/n)] = sha(R/n)
for rel in origins:
    bindings[str(L/rel)] = sha(L/rel)
# Work src must remain editable for review-only audit additions; immutable author copies already bound.
bindings = {n:v for n,v in bindings.items() if not n.startswith(str(L/'src')+'/')}
for n in ['env.sh','display_log.py','ROOT-PREP.json','INPUT-ORIGINS.json','SOURCE-ORDER.json','TASK.txt']:
    bindings[str(L/n)] = sha(L/n)
save(L/'frozen-inputs.json', bindings)
save(ROOT/'cmdrr-review-r5-ready.json', dict(utc=now, lane=str(L), task_sha256=sha(L/'TASK.txt'), frozen_bindings=len(bindings),
    copied_files=len(origins), modules=len(order), parent_integration=str(parent), model='gpt-6.1-sol', service='default', reasoning='high', credit=0))
print(json.dumps(dict(parent=str(parent), manifest=len(files), frozen=len(frozen), receipt_count=len(receipts), exits=dict(collections.Counter(str(x['exit']) for x in receipts)), review_lane=str(L), review_frozen=len(bindings), modules=len(order))))
