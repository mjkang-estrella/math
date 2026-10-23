"""Bounded integration and read-only verification for this specific intake."""
from pathlib import Path
import copy
import datetime
import fnmatch
import hashlib
import json
import stat
import subprocess
import sys

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
O = Path(__file__).resolve().parent
A = B / 'fresh-arithmetic-discovery-r162c'
TP = B / 'tasks.json'
JP = P / 'frontier/NEW-TEN-2026-10-14.md'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def read(path):
    return json.loads(path.read_bytes())

def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def git(*args):
    return subprocess.check_output(['git', *args], cwd=P)

base = read(O / 'integration-baseline.json')
intake = read(O / 'intake.json')
terminal = read(O / 'task-status.json')['structuredContent']
raw = read(O / 'arithmetic-r162d-dispatch.json')
r = raw['structuredContent']
request = read(O / 'private/submitted-prompt.json')
iso = read(O / 'prospective-isolation-arithmetic162d.json')
old_bytes = git('show', base['head'] + ':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json')
old_journal = git('show', base['head'] + ':openai-proof-research/frontier/NEW-TEN-2026-10-14.md')
assert sha(old_bytes) == base['tasks_sha256'] and sha(old_journal) == base['journal_sha256']
assert len(old_journal) == base['journal_bytes']
old = json.loads(old_bytes)
assert len(old['tasks']) == base['tasks'] == 656
assert terminal['taskId'] == old['tasks'][654]['taskId'] and terminal['status'] == 'completed'
assert not raw.get('isError') and r['status'] == 'running' and r['workState'] == 'working'
for result in [terminal, r]:
    assert (result['providerInstanceId'], result['model']) == ('codex', 'gpt-6-astra')
    assert {x['id']: x['value'] for x in result['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
    assert not result['hasPendingChildRuns'] and not result['hasPendingQuestion'] and result['pendingApproval'] is None
brief = (P / iso['new_brief']['path']).read_bytes()
assert brief.decode() == request['task'] and sha(brief) == iso['new_brief']['sha256'] and len(brief) == iso['new_brief']['bytes']
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = brief.split(marker, 1)[1]
assert len(suffix) == 5570 and suffix == (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162c-brief.txt').read_bytes().split(marker, 1)[1]
assert b'*t185144-*' in brief and b'*k369134-*' in brief
for peer in iso['existing_peer_original_initial_briefs']:
    data = (P / peer['brief']).read_bytes()
    assert sha(data) == peer['sha256'] and b'*arithmetic*r162*' in data
assert fnmatch.fnmatchcase('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162d/packet/FINAL.md', '*arithmetic*r162*')
assert sha((O / 'assessment.md').read_bytes()) == intake['assessment_sha256']
for relative, expected in intake['outside_anchors'].items():
    assert sha((A / relative).read_bytes()) == expected
assert intake['status'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED' and not intake['accepted'] and intake['count_change'] == 0
assert intake['correctness_review'] == intake['contribution_review'] == 'NOT_STARTED_NO_NOMINEE'
assert intake['downstream'] == 'NOT_STARTED_NO_NOMINEE' and intake['publication'] == 'STOPPED'
root = {x.relative_to(A).as_posix(): {'bytes': x.stat().st_size, 'sha256': sha(x.read_bytes()), 'mode': stat.S_IMODE(x.stat().st_mode)} for x in A.rglob('*') if x.is_file()}
assert not any(x.is_symlink() for x in A.rglob('*'))
assert root == read(O / 'private/root-baseline.json') and len(root) == 74
manifest = read(A / 'MANIFEST.json')
assert len(manifest['files']) == 62 and sum(x['bytes'] for x in manifest['files']) == 6418794
assert {x['path'] for x in manifest['files']} == {x.removeprefix('packet/') for x in root if x.startswith('packet/') and x != 'packet/MANIFEST.json'}
for row in manifest['files']:
    observed = root['packet/' + row['path']]
    assert (observed['bytes'], observed['sha256']) == (row['bytes'], row['sha256'])
assert read(O / 'artifact-verification.json')['exit'] == 0 and read(O / 'finite-checks.json')['all_checks_passed']
tree_bytes = (P / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_bytes) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_bytes)
assert len(tree['tree']) == 13223 and not tree['truncated']
nav = read(O / 'private/source067-navigation.json')
entries = [x for x in tree['tree'] if any(x['path'].startswith(f + '/') for f in nav['family_manuscript_folders'])]
assert entries == nav['entries'] and len(entries) == 18 and sum(x['type'] == 'blob' for x in entries) == 15 and len(nav['family_manuscript_folders']) == 1
assert not nav['parent_read_source_proofs']
selection = read(O / 'private/source067-selection.json')
start, end = selection['catalogue_extent']
with (P / 'sources/CONTENTS.md').open('rb') as stream:
    stream.seek(start)
    selected = stream.read(end - start)
assert selected == (O / 'private/catalogue-067.md').read_bytes() and sha(selected) == selection['selected_sha256']
for relative, expected in base['protected_unrelated_sha256'].items():
    assert sha((P / relative).read_bytes()) == expected

if sys.argv[1] == 'integrate':
    assert git('rev-parse', 'HEAD').decode().strip() == base['head']
    assert TP.read_bytes() == old_bytes and JP.read_bytes() == old_journal
    assert not git('diff', '--cached', '--name-only')
    assert all(x.get('taskId') != r['taskId'] for x in old['tasks'])
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    new = copy.deepcopy(old)
    new['tasks'][654].update(terminal)
    new['tasks'][654].update({'parent_full_intake_pending': False, 'parent_disposition': intake['status'], 'parent_intake': str((O / 'intake.json').relative_to(B)), 'parent_assessment_sha256': intake['assessment_sha256'], 'parent_intake_utc': now, 'status_provenance': 'Actual single notified terminal task_status response, archived raw.', 'accepted': False, 'count_change': 0})
    task = copy.deepcopy(r)
    task.update({'observed_utc': now, 'target': request['target'], 'role': request['role'], 'title': request['title'], 'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162d/', 'brief': iso['new_brief']['path'], 'brief_sha256': iso['new_brief']['sha256'], 'brief_bytes': iso['new_brief']['bytes'], 'source_family_navigation': 'Source067; exact catalogue[114746,115750), one CP-sixfold folder,18 descendants/15 blobs. Metadata navigation only; actual proof reading assigned.', 'round_namespace': 'NEW DISTINCT family under the already excluded arithmetic162 namespace, not a retry of162 or162c.', 'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED', 'dispatch_receipt': str((O / 'arithmetic-r162d-dispatch.json').relative_to(B)), 'prospective_isolation': str((O / 'prospective-isolation-arithmetic162c.json').relative_to(B)), 'clientRequestId': request['clientRequestId'], 'round': 1, 'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177', 'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.'})
    new['tasks'].append(task)
    note = 'Arithmetic162c(idx654, Source066) completed PREFREEZE/no nominee and archived: bounded-index additive discrepancy/base-order buffer retained, while uniform multiplicative retention at unbounded original discrepancy and vanishing normalized base order remains unpaid. Exact62-file verification and33 canonical blob checks passed; no grade/count. Arithmetic162d(idx656, DISTINCT Source067 Campana-Peternell sixfold family) dispatched with Astra high/default within the already excluded162 namespace. Owner archive of Structural194(idx652), foreign Structural195(idx655), and prior archives preserved without query/body inspection/steering. Campaign19/20, latestR041, one remains; publication STOPPED.'
    new['last_parent_progress'] = note
    snapshot = new['current_work_snapshot']
    snapshot.update({'observed_utc': now, 'note': note, 't3_current_confirmed_running': [r['taskId']], 'fresh_discovery_current': [task['output']], 't3_last_polled_running_note': 'Historical foreign-owner list retained. Own current confirmed list is based on Arithmetic162c dispatch; no new Structural195 liveness check.', 'arithmetic_r162c_archive': {'task_index': 654, 'status': intake['status'], 'intake': str((O / 'intake.json').relative_to(B)), 'accepted': False, 'count_change': 0}})
    snapshot['t3_recorded_running_different_owner'] = [{'task_index': 655, 'taskId': old['tasks'][655]['taskId'], 'parent_thread': old['tasks'][655]['parent_thread'], 'shared_record_status': old['tasks'][655]['status'], 'current_thread_status_request': 'not_requested_foreign_owner', 'current_liveness_verified_here': False, 'action': 'Preserved without query, body/activity inspection, steering or duplicate dispatch.'}]
    snapshot['t3_dispatch_observations'].append({'observed_utc': now, **copy.deepcopy(r)})
    changes = {'baseline': base['head'], 'old_tasks': 656, 'new_tasks': 657, 'changed_old_task_indices': [i for i in range(656) if old['tasks'][i] != new['tasks'][i]], 'changed_snapshot_keys': sorted(k for k in set(old['current_work_snapshot']) | set(snapshot) if old['current_work_snapshot'].get(k) != snapshot.get(k)), 'count_change': 0, 'foreign_task_record_unchanged': old['tasks'][652] == new['tasks'][652]}
    assert changes['changed_old_task_indices'] == [654]
    dump(O / 'integration-changes.json', changes)
    appendix = '\n\n### 2026-10-22: Arithmetic162c archive; distinct Arithmetic162d discovery\n\nArithmetic162c(idx654, Source066) completed PREFREEZE/no nominee and archived: bounded-index additive discrepancy/base-order buffer retained, while uniform multiplicative retention at unbounded original discrepancy and vanishing normalized base order remains unpaid. Exact62-file verification and33 canonical blob checks passed; no grade/count. Arithmetic162d(idx656, DISTINCT Source067 Campana-Peternell sixfold family) dispatched with Astra high/default within the already excluded162 namespace. Owner archive of Structural194(idx652), foreign Structural195(idx655), and prior archives preserved without query/body inspection/steering. Campaign19/20, latestR041, one remains; publication STOPPED.\n\nThe unchanged target requires one bounded-index complement retaining a uniform fraction of EVERY original discrepancy. The constructed additive buffer, complete-system fixed-part reduction, vertical subtraction, averaging/powers and exact-character compatibility analysis remain retained. No uniform fixed-part margin is proved. All authored derivations and reading limits were read; source/primary semantic extents remain author records, not a fresh parent review. The74-file root stayed unchanged. Canonical clipping recovery, selective primary proofs, late image checks, false helper admissions and coarse omissions remain disclosed.\n\nSource067 is one new distinct family; both its Fano-sixfold classification and stated augmented-irregularity universal-cover corollary are paid. Actual operative proof reading is assigned. The initial foreign peer brief already excluded the entire162d namespace; no live peer body/activity/finding/status was inspected and no peer was steered. Protected private bodies and named metadata remain unstaged. See discovery-arithmetic-r162c-parent/assessment.md and intake.json.\n'
    (O / 'private/journal-append.bin').write_bytes(appendix.encode())
    assert TP.read_bytes() == old_bytes and JP.read_bytes() == old_journal and git('rev-parse', 'HEAD').decode().strip() == base['head']
    dump(TP, new)
    JP.write_bytes(old_journal + appendix.encode())
    print(json.dumps(changes))
else:
    committed = '--committed' in sys.argv
    assert git('rev-parse', 'HEAD^' if committed else 'HEAD').decode().strip() == base['head']
    new = read(TP)
    changes = read(O / 'integration-changes.json')
    assert len(new['tasks']) == 657 and [i for i in range(656) if old['tasks'][i] != new['tasks'][i]] == changes['changed_old_task_indices'] == [654]
    assert {k: v for k, v in old.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')} == {k: v for k, v in new.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')}
    s, t = old['current_work_snapshot'], new['current_work_snapshot']
    assert sorted(k for k in set(s) | set(t) if s.get(k) != t.get(k)) == changes['changed_snapshot_keys']
    assert t['t3_recorded_running_different_owner'][0]['task_index'] == 655 and not t['t3_recorded_running_different_owner'][0]['current_liveness_verified_here']
    assert (new['newAccepted'], new['target'], new['remaining'], new['latestAcceptance']) == (19, 20, 1, 'R041') and not t['user_pause_requested']
    assert new['tasks'][654]['parent_disposition'] == intake['status'] and new['tasks'][654]['status'] == 'completed' and not new['tasks'][654]['accepted'] and new['tasks'][654]['count_change'] == 0
    assert new['tasks'][656]['taskId'] == r['taskId'] and not new['tasks'][656]['accepted'] and new['tasks'][656]['count_change'] == 0
    assert t['t3_current_confirmed_running'] == [r['taskId']] and t['t3_dispatch_observations'][:-1] == s['t3_dispatch_observations']
    assert JP.read_bytes() == old_journal + (O / 'private/journal-append.bin').read_bytes()
    allow = read(O / 'stage-allowlist.json')
    expected_names = {'openai-proof-research/' + x for x in allow}
    assert len(expected_names) == len(allow) and not any('/private/' in x or '/controls/' in x or x.endswith('/MANIFEST.json') or '/fresh-arithmetic-discovery-r162d/' in x for x in allow)
    assert all((P / x).is_file() for x in allow)
    if '--staged' in sys.argv or committed:
        names = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines()) if committed else set(git('diff', '--cached', '--name-only').decode().splitlines())
        assert names == expected_names
        for relative in allow:
            assert git('show', ('HEAD:' if committed else ':') + 'openai-proof-research/' + relative) == (P / relative).read_bytes()
    expected_diff = {'openai-proof-research/' + x for x in base['protected_unrelated_sha256']}
    if '--staged' not in sys.argv and not committed:
        expected_diff |= {'openai-proof-research/frontier/campaigns/2026-10-14/tasks.json', 'openai-proof-research/frontier/NEW-TEN-2026-10-14.md'}
    assert set(git('diff', '--name-only').decode().splitlines()) == expected_diff
    print(json.dumps({'result': 'MATCH', 'changed_old_tasks': [654], 'new_task': 656, 'tasks': 657, 'packet_files': 62, 'immutable_root_files': 74, 'new_source_folders': 1, 'new_source_descendants': 18, 'new_source_blobs': 15, 'standing_suffix_bytes': 5570, 'count': '19/20', 'count_change': 0, 'allowlist_files': len(allow), 'mode': 'committed' if committed else 'staged' if '--staged' in sys.argv else 'working'}))
