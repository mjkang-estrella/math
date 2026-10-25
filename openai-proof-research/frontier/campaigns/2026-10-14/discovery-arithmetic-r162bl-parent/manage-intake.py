#!/usr/bin/env python3
"""CAS archive r162bl and register the distinct standard-speed Source146 round."""
from pathlib import Path
from datetime import datetime, timezone
import copy, fnmatch, hashlib, json, re, subprocess
P = Path(__file__).resolve().parents[4]; D = Path(__file__).resolve().parent; B = D.parent
N = B / 'discovery-arithmetic-r162bm-parent'; R = B / 'fresh-arithmetic-discovery-r162bl'
TP = 'frontier/campaigns/2026-10-14/tasks.json'; JP = 'frontier/NEW-TEN-2026-10-14.md'
def git(*args): return subprocess.check_output(['git', *args], cwd=P)
def sha(a): return hashlib.sha256(a).hexdigest()
def dump(p, x): p.write_text(json.dumps(x, ensure_ascii=False, indent=2) + '\n')
def snapshot(root):
    out = {}
    for f in root.rglob('*'):
        assert not f.is_symlink()
        if f.is_file():
            a = f.read_bytes(); out[f.relative_to(root).as_posix()] = dict(bytes=len(a), sha256=sha(a), mode=f.stat().st_mode)
    return out

assert not git('diff', '--cached', '--name-only').strip()
head = git('rev-parse', 'HEAD').decode().strip()
raw_t = git('show', head + ':openai-proof-research/' + TP)
raw_j = git('show', head + ':openai-proof-research/' + JP)
assert (P / TP).read_bytes() == raw_t and (P / JP).read_bytes() == raw_j, 'Concurrent uncommitted coordination; no overwrite.'
old = json.loads(raw_t); new = copy.deepcopy(old)
baseline = json.loads((D / 'intake-baseline.json').read_bytes())
assert old['newAccepted'] == 19 and old['target'] == 20 and old['latestAcceptance'] == 'R041'
assert old['gpt_subagent_preferences']['serviceTier'] == 'default'
own = next(i for i, x in enumerate(old['tasks']) if x.get('clientRequestId') == 'twenty-20261024-fresh-arithmetic-r162bl-codex-astra-r1')
assert own == 815 and old['tasks'][own]['status'] == 'running'
client = 'twenty-20261024-fresh-arithmetic-r162bm-codex-astra-r1'
assert not any(x.get('clientRequestId') == client for x in old['tasks'])
for n, h in baseline['protected'].items(): assert sha((P / n).read_bytes()) == h
guard = json.loads((N / 'prospective-isolation.json').read_bytes()); checks = []
for i, x in enumerate(old['tasks']):
    if i == own or x.get('status') not in {'running', 'queued', 'waiting'} or not x.get('brief'): continue
    a = (P / x['brief']).read_bytes()
    assert not x.get('brief_sha256') or sha(a) == x['brief_sha256']
    patterns = [z for z in re.findall(r'\*[^\s,;()]*\*', a.decode()) if z not in {'*', '**'}]
    matches = {n: sorted(z for z in patterns if fnmatch.fnmatchcase(n.casefold(), z.casefold())) for n in guard['namespaces']}
    assert all(matches.values())
    checks.append(dict(task_index=i, original_brief=x['brief'], sha256=sha(a), matches=matches))

terminal = json.loads((D / 'task-status.json').read_bytes())['structuredContent']
dispatch = json.loads((N / 'dispatch.json').read_bytes())['structuredContent']
assert terminal['taskId'] == old['tasks'][own]['taskId'] and terminal['status'] == 'completed' and terminal['workState'] == 'result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
assert dispatch['status'] == 'running' and dispatch['workState'] == 'working'
assert dispatch['providerInstanceId'] == 'codex' and dispatch['model'] == 'gpt-6-astra'
assert {x['id']: x['value'] for x in dispatch['options']} == dict(reasoningEffort='high', serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
prep = json.loads((N / 'brief-preparation.json').read_bytes()); brief = (P / prep['brief']).read_bytes()
assert len(brief) == prep['bytes'] and sha(brief) == prep['sha256'] and len(brief.decode()) < 120000
assert prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified'] and prep['standing_bytes_preserved'] == 5570
v = json.loads((D / 'verification.json').read_bytes()); intake = json.loads((D / 'intake.json').read_bytes())
assert v['status'] == 'MATCH' and v['bundled_verifier_passed'] and v['whole_root_bytes_and_full_modes_unchanged']
assert intake['disposition'] == 'PREFREEZE_NO_NOMINEE'
assert snapshot(R) == json.loads((D / 'private/intake/root-before.json').read_bytes())
now = datetime.now(timezone.utc).isoformat()
rec = new['tasks'][own]; rec.update(terminal)
rec.update(observed_utc=now, disposition='PREFREEZE_NO_NOMINEE', parent_intake='discovery-arithmetic-r162bl-parent/intake.json', parent_assessment='discovery-arithmetic-r162bl-parent/assessment.md', artifact_verification='discovery-arithmetic-r162bl-parent/verification.json', artifact_status='MATCH', bundled_verifier_passed=True, sealed_author_root_unchanged=True, no_new_diagnostic_selected=True, full_scopes_preserved=True, frozen_statement=False, author_proof_nominee=False, correctness_gate=None, contribution_gate=None, accepted=False, count_change=0, full_diagnostic=None, diagnostic_record=intake['diagnostic_record'], diagnostic_record_sha256=intake['diagnostic_record_sha256'], diagnostic_selected=False, paid_reduction=intake['paid_reduction'], retained_mathematics=intake['retained_mathematics'], unpaid_obligation=intake['unpaid_obligation'], canonical_text_objects_read_and_authenticated=22, canonical_text_bytes=248343, canonical_folder_blobs=24, canonical_entries=31, paid_source_companion=145, vendor_runtime_blobs=0, compiled_pdfs_authentication_only=2, primary_objects=3, primary_distinct_pages_touched=66, primary_full_extracted_papers=1, primary_visual_pages=3, transitive_primary_reading_complete=False, optional_original_history_traversals=0, author_initial_context_full_modes_recorded=False, author_initial_context_permission_bits_matched=True, parent_predispatch_ledger_original_full_modes_matched=True, mode_record_limitation_preserved=True, parent_full_intake_pending=False, status_provenance='Own terminal task_status queried once. Complete author comparison,working/context,reading limits,handoffs and verifier read;not an independent source/primary proof rereading. Artifact checks separate;no mathematical grades or foreign liveness query.')
fresh = copy.deepcopy(dispatch)
fresh.update(observed_utc=now, role='research', round=1, title='Arithmetic162bm: confirmed standard-map metric-entropy discovery', clientRequestId=client, parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177', target=dict(providerInstanceId='codex', model='gpt-6-astra', options=dict(reasoningEffort='high', serviceTier='default')), output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bm/', brief=prep['brief'], brief_sha256=prep['sha256'], brief_bytes=prep['bytes'], submitted_prompt_contains_full_brief=True, source_index=146, source_family_navigation='Exact catalogue[241294,242223). One bounded14000-byte window at240464 decoded titles/bodies145 and146;147heading only boundary. Source145 already read/paid as r162bl companion and deliberately skipped. Selected1root12blobs16entries11texts145989bytes;actual build/paper.tex2705/Gitd685d6f3d32384a77d2de437b5660d2846015574. Parent operative proof not read.', round_namespace='Fresh distinct standard-map metric-entropy research. Entire original standard sine map full sufficiently-large positive parameter tail of positive normalized-area metric entropy is paid. All stronger actual geometric,recurrence,inducing,parameter and measure operations require reading. No replacement by topological entropy,some hyperbolic set,some invariant measure,selected points or parameter subset. Older full scopes unchanged.', all_previous_literal_guards_and5570_standing_bytes_retained=True, all_new_literal_guard_twins_verified_before_dispatch=True, completed_direct_inputs=5, dispatch_receipt='discovery-arithmetic-r162bm-parent/dispatch.json', prospective_isolation='discovery-arithmetic-r162bm-parent/prospective-isolation.json', prompt_length_checked_before_dispatch=True, historical_context_compacted='Completed r162bl intake summarized;old guard literals,5570 standing bytes and old full scopes retained. Source145 paid companion deliberately skipped.', distinct_family=True, new_author_conversation=True, independent_review=False, accepted=False, count_change=0, parent_count_at_dispatch=19, publication='STOPPED', status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default,matching latest user standard-speed instruction. No polling,watcher or foreign liveness query.')
new_index = len(new['tasks']); new['tasks'].append(fresh)
note = 'Arithmetic162bl archived PREFREEZE/no nominee. Same-map all-point/all-jet subexponential growth,zero topological entropy,smooth cyclicity and finite-stage bounded exact whitening close as source/classical comparisons;uniform regularity through infinite whitening remains unproved/unfrozen. Both canonical proofs22texts248343bytes read,24blobs31entries;3primaries66touched pages(somepartial),one full26page paper,3renders,ancestry incomplete,history0. Parent/bundled artifact MATCH64payloads66files11dirs unchanged;initial permission-only record remains qualified. No gates/count. Source145 already paid companion skipped;Source146 standard-map metric-entropy Arithmetic162bm dispatched Codex/GPT-6 Astra/high/default. Campaign19/20,latestR041;all old scopes preserved;publication STOPPED.'
new['last_parent_progress'] = note
snap = new['current_work_snapshot']; snap.update(observed_utc=now, note=note)
snap['arithmetic_r162bl_archive'] = dict(task_index=own, intake='discovery-arithmetic-r162bl-parent/intake.json', disposition='PREFREEZE_NO_NOMINEE', frozen_statement=False, no_new_diagnostic_selected=True, diagnostic_selected=False, correctness_gate=None, contribution_gate=None, accepted=False, count_change=0)
snap['arithmetic_r162bm_dispatch'] = dict(task_index=new_index, taskId=dispatch['taskId'], status=dispatch['status'], brief=prep['brief'], source=146, catalogue_extent=[241294,242223], skipped_paid_source=145, serviceTier='default', distinct_family=True, original_brief_guards_checked_before_creation=True, both_new_literal_twins_verified=True, new_family_screens=2, private_local_inputs_and_metadata_retained=True, foreign_live_queries=False, count_change=0, publication='STOPPED')
changed = [i for i, (x, y) in enumerate(zip(old['tasks'], new['tasks'])) if x != y]
assert changed == [own] and len(new['tasks']) == len(old['tasks']) + 1
assert all(new[k] == old[k] for k in old if k not in {'tasks', 'last_parent_progress', 'current_work_snapshot'})
allowed = {'observed_utc', 'note', 'arithmetic_r162bl_archive', 'arithmetic_r162bm_dispatch'}
assert all(snap[k] == x for k, x in old['current_work_snapshot'].items() if k not in allowed)
addition = ('\n\n### Arithmetic162bl archive and standard-map dispatch — ' + now + '\n\n' + note + '\n\n' + 'The [parent assessment](campaigns/2026-10-14/discovery-arithmetic-r162bl-parent/assessment.md) preserves the complete author comparison and exact evidence limits. Source144 entire smooth standard-volume T3/simple-Lebesgue real-generator construction and fully read Source145 multiple-mixing companion operations are paid. Uniform derivative-growth and smooth cyclicity comparisons do not supply physical norm control for infinite exact whitening;L2 convergence and finite-stage bounds do not settle the joint estimate. No theorem/diagnostic frozen,no independent correctness/contribution gate,no count. Parent read full21,639-byte comparison,13,086-byte limits,working/context,handoffs and verifier;source/primary proofs were not independently reread. Canonical22texts248343bytes24blobs31entries verified;2compiledPDFsauthonly. Threeprimaries66distinct touchedpages(somepartial),onefull26page paper,3renders;late recoveries,404/non-PDF access failures,unused incidental snippets and incomplete ancestry disclosed. History0,five direct exceptions only. Parent/bundled exact artifact checks MATCH64payloads3951719bytes66files11dirs,24Gitblobs,3primaryPDF/extractpairs,5original/copy pairs. Initial author permissions-only bindings remain qualified;later full modes and separate parent pre-dispatch full modes match. Three wrong anchors rejected,restoredtinycontrolpassed;allsealedbytes/modesunchanged. Next catalogue window240464..254464 decoded two bodies145/146 only;Source145 skipped as already paid,147headingboundaryonly. Source146 exact241294..242223,one root12blobs16entries11texts145989bytes,actualbuild/paper.tex2705/Gitd685d6f3d32384a77d2de437b5660d2846015574. Full original standard-map large-positive-parameter-tail normalized-area metric entropy is stipulated and paid;new round must read strongest actual proof interfaces before an additional theorem. Standard/default tier verified in actual dispatch;all literal guards and5570standingbytes retained. No polling/watcher,foreign liveness query or downstream/public work. Other tasks,unrelated modifications,old scopes and journal prefix preserved.\n').encode()
next_t = (json.dumps(new, ensure_ascii=False, indent=2) + '\n').encode(); next_j = raw_j + addition
dump(D / 'coordination-rebase.json', dict(intake_head=baseline['head'], integration_head=head, head_advanced=head != baseline['head'], before_task_count=len(old['tasks']), after_task_count=len(new['tasks']), changed_old_task_indices=changed, new_task_index=new_index, all_other_tasks_preserved=True, all_other_top_fields_preserved=True, journal_prefix_preserved=True, protected_modifications_preserved=True, tasks_before_sha256=sha(raw_t), tasks_after_sha256=sha(next_t), journal_before_sha256=sha(raw_j), journal_after_sha256=sha(next_j), integration_original_brief_guard_checks=checks, no_foreign_live_queries=True))
dump(N / 'registration.json', dict(task_index=new_index, taskId=dispatch['taskId'], status_at_dispatch=dispatch['status'], distinct_family=True, model_options_verified=True, count_change=0, publication='STOPPED'))
(D / 'private/intake/our-tasks-after.json').write_bytes(next_t)
(D / 'private/intake/our-journal-after.md').write_bytes(next_j)
for e in json.loads((N / 'private/completed-direct-inputs.json').read_bytes()):
    f = P / e['path']; a = f.read_bytes()
    assert len(a) == e['bytes'] and sha(a) == e['sha256'] and f.stat().st_mode == e['mode']
assert git('rev-parse', 'HEAD').decode().strip() == head and (P / TP).read_bytes() == raw_t and (P / JP).read_bytes() == raw_j
(P / TP).write_bytes(next_t); (P / JP).write_bytes(next_j)
names = ['assessment.md', 'intake.json', 'verification.json', 'verify-intake.py', 'task-status.json', 'intake-baseline.json', 'intake-prospective-isolation.json', 'integration-guard.json', 'prepare-next.py', 'manage-intake.py', 'coordination-rebase.json']
paths = [(D / n).relative_to(P).as_posix() for n in names] + [(N / n).relative_to(P).as_posix() for n in ['brief-preparation.json', 'capabilities.json', 'dispatch.json', 'prospective-isolation.json', 'registration.json']] + [prep['brief'], TP, JP]
assert len(paths) == len(set(paths)) == 19
assert git('rev-parse', 'HEAD').decode().strip() == head and (P / TP).read_bytes() == next_t and (P / JP).read_bytes() == next_j
subprocess.run(['git', 'add', '--', *paths], cwd=P, check=True)
assert {x for x in git('diff', '--cached', '--name-only', '-z').decode().split('\0') if x} == {'openai-proof-research/' + n for n in paths}
for n in paths: assert git('show', ':openai-proof-research/' + n) == (P / n).read_bytes()
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=P, check=True)
assert git('rev-parse', 'HEAD').decode().strip() == head
subprocess.run(['git', 'commit', '-m', 'Archive smooth-spectrum comparisons and start standard-map research'], cwd=P, check=True)
assert not git('diff', '--cached', '--name-only').strip()
assert snapshot(R) == json.loads((D / 'private/intake/root-before.json').read_bytes())
assert git('show', 'HEAD:openai-proof-research/' + TP) == next_t and git('show', 'HEAD:openai-proof-research/' + JP) == next_j
for n, h in baseline['protected'].items(): assert sha((P / n).read_bytes()) == h
print(json.dumps(dict(commit=git('rev-parse', 'HEAD').decode().strip(), changed_old_tasks=changed, new_task_index=new_index, all_other_tasks_preserved=True, staged_allowed_paths=19, campaign_count=19, index_empty=True, sealed_author_root_unchanged=True, protected_modifications_preserved=True)))
