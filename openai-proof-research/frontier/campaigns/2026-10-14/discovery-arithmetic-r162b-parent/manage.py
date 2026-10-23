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
A = B / 'fresh-arithmetic-discovery-r162b'
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
raw = read(O / 'arithmetic-r162c-dispatch.json')
r = raw['structuredContent']
request = read(O / 'private/submitted-prompt.json')
iso = read(O / 'prospective-isolation-arithmetic162c.json')
old_bytes = git('show', base['head'] + ':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json')
old_journal = git('show', base['head'] + ':openai-proof-research/frontier/NEW-TEN-2026-10-14.md')
assert sha(old_bytes) == base['tasks_sha256'] and sha(old_journal) == base['journal_sha256']
assert len(old_journal) == base['journal_bytes']
old = json.loads(old_bytes)
assert len(old['tasks']) == base['tasks'] == 654
assert terminal['taskId'] == old['tasks'][653]['taskId'] and terminal['status'] == 'completed'
assert not raw.get('isError') and r['status'] == 'running' and r['workState'] == 'working'
for result in [terminal, r]:
    assert (result['providerInstanceId'], result['model']) == ('codex', 'gpt-6-astra')
    assert {x['id']: x['value'] for x in result['options']} == {'reasoningEffort': 'high', 'serviceTier': 'default'}
    assert not result['hasPendingChildRuns'] and not result['hasPendingQuestion'] and result['pendingApproval'] is None
brief = (P / iso['new_brief']['path']).read_bytes()
assert brief.decode() == request['task'] and sha(brief) == iso['new_brief']['sha256'] and len(brief) == iso['new_brief']['bytes']
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = brief.split(marker, 1)[1]
assert len(suffix) == 5570 and suffix == (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162b-brief.txt').read_bytes().split(marker, 1)[1]
assert b'*t185144-*' in brief and b'*k369134-*' in brief
for peer in iso['existing_peer_original_initial_briefs']:
    data = (P / peer['brief']).read_bytes()
    assert sha(data) == peer['sha256'] and b'*arithmetic*r162*' in data
assert fnmatch.fnmatchcase('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162c/packet/FINAL.md', '*arithmetic*r162*')
assert sha((O / 'assessment.md').read_bytes()) == intake['assessment_sha256']
for relative, expected in intake['outside_anchors'].items():
    assert sha((A / relative).read_bytes()) == expected
assert intake['status'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED' and not intake['accepted'] and intake['count_change'] == 0
assert intake['correctness_review'] == intake['contribution_review'] == 'NOT_STARTED_NO_NOMINEE'
assert intake['downstream'] == 'NOT_STARTED_NO_NOMINEE' and intake['publication'] == 'STOPPED'
root = {x.relative_to(A).as_posix(): {'bytes': x.stat().st_size, 'sha256': sha(x.read_bytes()), 'mode': stat.S_IMODE(x.stat().st_mode)} for x in A.rglob('*') if x.is_file()}
assert not any(x.is_symlink() for x in A.rglob('*'))
assert root == read(O / 'private/root-baseline.json') and len(root) == 80
manifest = read(A / 'packet/MANIFEST.json')
assert len(manifest['files']) == 69 and sum(x['bytes'] for x in manifest['files']) == 9864381
assert {x['path'] for x in manifest['files']} == {x.removeprefix('packet/') for x in root if x.startswith('packet/') and x != 'packet/MANIFEST.json'}
for row in manifest['files']:
    observed = root['packet/' + row['path']]
    assert (observed['bytes'], observed['sha256']) == (row['bytes'], row['sha256'])
assert read(O / 'artifact-verification.json')['exit'] == 0 and read(O / 'finite-checks.json')['all_checks_passed']
tree_bytes = (P / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_bytes) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_bytes)
assert len(tree['tree']) == 13223 and not tree['truncated']
nav = read(O / 'private/source066-navigation.json')
entries = [x for x in tree['tree'] if any(x['path'].startswith(f + '/') for f in nav['family_manuscript_folders'])]
assert entries == nav['entries'] and len(entries) == 39 and sum(x['type'] == 'blob' for x in entries) == 33 and len(nav['family_manuscript_folders']) == 2
assert not nav['parent_read_source_proofs']
selection = read(O / 'private/source066-selection.json')
start, end = selection['catalogue_extent']
with (P / 'sources/CONTENTS.md').open('rb') as stream:
    stream.seek(start)
    selected = stream.read(end - start)
assert selected == (O / 'private/catalogue-066.md').read_bytes() and sha(selected) == selection['selected_sha256']
for relative, expected in base['protected_unrelated_sha256'].items():
    assert sha((P / relative).read_bytes()) == expected

if sys.argv[1] == 'integrate':
    assert git('rev-parse', 'HEAD').decode().strip() == base['head']
    assert TP.read_bytes() == old_bytes and JP.read_bytes() == old_journal
    assert not git('diff', '--cached', '--name-only')
    assert all(x.get('taskId') != r['taskId'] for x in old['tasks'])
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    new = copy.deepcopy(old)
    new['tasks'][653].update(terminal)
    new['tasks'][653].update({'parent_full_intake_pending': False, 'parent_disposition': intake['status'], 'parent_intake': str((O / 'intake.json').relative_to(B)), 'parent_assessment_sha256': intake['assessment_sha256'], 'parent_intake_utc': now, 'status_provenance': 'Actual single notified terminal task_status response, archived raw.', 'accepted': False, 'count_change': 0})
    task = copy.deepcopy(r)
    task.update({'observed_utc': now, 'target': request['target'], 'role': request['role'], 'title': request['title'], 'output': 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162c/', 'brief': iso['new_brief']['path'], 'brief_sha256': iso['new_brief']['sha256'], 'brief_bytes': iso['new_brief']['bytes'], 'source_family_navigation': 'Source066; exact catalogue[112793,114746), two complements/Cartier canonical folders,39 descendants/33 blobs. Metadata navigation only; actual proof reading assigned.', 'round_namespace': 'NEW DISTINCT family under the already excluded arithmetic162 namespace, not a retry of162 or162b.', 'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0, 'publication': 'STOPPED', 'dispatch_receipt': str((O / 'arithmetic-r162c-dispatch.json').relative_to(B)), 'prospective_isolation': str((O / 'prospective-isolation-arithmetic162c.json').relative_to(B)), 'clientRequestId': request['clientRequestId'], 'round': 1, 'parent_thread': '6742db91-d35c-44d0-a762-e5d9232f5177', 'status_provenance': 'Actual successful delegate_task response; running at dispatch, not a later liveness poll.'})
    new['tasks'].append(task)
    note = 'Arithmetic162b(idx653, Source065) completed PREFREEZE/no nominee and archived: full mixed relative Virasoro intertwiner with vanishing cap-image residual, all modes/cutoffs, scalar normalization and integral-class gluing remains unpaid. Exact69-file verification,26 canonical blob checks and finite algebra checks passed; no grade/count. Arithmetic162c(idx654, DISTINCT Source066 complements/Cartier companions) dispatched with Astra high/default within the already excluded162 namespace. Foreign Structural194(idx652) and prior archives preserved without query/body inspection/steering. Campaign19/20, latestR041, one remains; publication STOPPED.'
    new['last_parent_progress'] = note
    snapshot = new['current_work_snapshot']
    snapshot.update({'observed_utc': now, 'note': note, 't3_current_confirmed_running': [r['taskId']], 'fresh_discovery_current': [task['output']], 't3_last_polled_running_note': 'Historical foreign-owner list retained. Own current confirmed list is based on Arithmetic162c dispatch; no new Structural194 liveness check.', 'arithmetic_r162b_archive': {'task_index': 653, 'status': intake['status'], 'intake': str((O / 'intake.json').relative_to(B)), 'accepted': False, 'count_change': 0}})
    snapshot['t3_dispatch_observations'].append({'observed_utc': now, **copy.deepcopy(r)})
    changes = {'baseline': base['head'], 'old_tasks': 654, 'new_tasks': 655, 'changed_old_task_indices': [i for i in range(654) if old['tasks'][i] != new['tasks'][i]], 'changed_snapshot_keys': sorted(k for k in set(old['current_work_snapshot']) | set(snapshot) if old['current_work_snapshot'].get(k) != snapshot.get(k)), 'count_change': 0, 'foreign_task_record_unchanged': old['tasks'][652] == new['tasks'][652]}
    assert changes['changed_old_task_indices'] == [653]
    dump(O / 'integration-changes.json', changes)
    appendix = ('\n\n### 2026-10-22: Arithmetic162b archive; distinct Arithmetic162c discovery\n\n' + note + '\n\nThe unchanged relative Ward scope retains every genus/integral class, arbitrary super/empty contact states, cap choice and ordinary gluing. Stable boundary grading, half shifts, exact image/row/commutator residuals and the explicit strict-diagonal rubber correction remain retained. No theorem was frozen. All authored derivations and exact reading limits were read; source/primary semantic extents remain author records, not a fresh parent review. The80-file root stayed unchanged. Published-version failures, late primary preliminaries and unread cap/loop proofs remain disclosed.\n\nSource066 is one distinct family with both complements/Cartier companions. The initial foreign peer brief already excluded the entire new162c namespace. No live peer body/activity/finding or status was inspected and no peer was steered. Actual new operative proof reading is assigned; all protected private bodies and named metadata remain unstaged. See discovery-arithmetic-r162b-parent/assessment.md and intake.json.\n')
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
    assert len(new['tasks']) == 655 and [i for i in range(654) if old['tasks'][i] != new['tasks'][i]] == changes['changed_old_task_indices'] == [653]
    assert {k: v for k, v in old.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')} == {k: v for k, v in new.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')}
    s, t = old['current_work_snapshot'], new['current_work_snapshot']
    assert sorted(k for k in set(s) | set(t) if s.get(k) != t.get(k)) == changes['changed_snapshot_keys']
    assert t['t3_recorded_running_different_owner'] == s['t3_recorded_running_different_owner']
    assert (new['newAccepted'], new['target'], new['remaining'], new['latestAcceptance']) == (19, 20, 1, 'R041') and not t['user_pause_requested']
    assert new['tasks'][653]['parent_disposition'] == intake['status'] and new['tasks'][653]['status'] == 'completed' and not new['tasks'][653]['accepted'] and new['tasks'][653]['count_change'] == 0
    assert new['tasks'][654]['taskId'] == r['taskId'] and not new['tasks'][654]['accepted'] and new['tasks'][654]['count_change'] == 0
    assert t['t3_current_confirmed_running'] == [r['taskId']] and t['t3_dispatch_observations'][:-1] == s['t3_dispatch_observations']
    assert JP.read_bytes() == old_journal + (O / 'private/journal-append.bin').read_bytes()
    allow = read(O / 'stage-allowlist.json')
    expected_names = {'openai-proof-research/' + x for x in allow}
    assert len(expected_names) == len(allow) and not any('/private/' in x or '/controls/' in x or x.endswith('/MANIFEST.json') or '/fresh-arithmetic-discovery-r162c/' in x for x in allow)
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
    print(json.dumps({'result': 'MATCH', 'changed_old_tasks': [653], 'new_task': 654, 'tasks': 655, 'packet_files': 69, 'immutable_root_files': 80, 'new_source_folders': 2, 'new_source_descendants': 39, 'new_source_blobs': 33, 'standing_suffix_bytes': 5570, 'count': '19/20', 'count_change': 0, 'allowlist_files': len(allow), 'mode': 'committed' if committed else 'staged' if '--staged' in sys.argv else 'working'}))
