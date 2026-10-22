"""Read-only checks for the bounded resume/dispatch integration."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
O = Path(__file__).resolve().parent
base = json.loads((O / 'integration-baseline.json').read_bytes())
record = json.loads((O / 'reconciliation.json').read_bytes())
allow = json.loads((O / 'stage-allowlist.json').read_bytes())

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=P)

def original(path):
    return git('show', base['head'] + ':openai-proof-research/' + path)

head = git('rev-parse', 'HEAD').decode().strip()
committed = '--committed' in sys.argv
assert (git('rev-parse', 'HEAD^').decode().strip() if committed else head) == base['head']
old_bytes = original('frontier/campaigns/2026-10-14/tasks.json')
assert sha(old_bytes) == base['tasks_sha256']
old = json.loads(old_bytes)
new = json.loads((B / 'tasks.json').read_bytes())
assert len(old['tasks']) == 648 and len(new['tasks']) == 649
assert new['tasks'][:648] == old['tasks']
assert {k: v for k, v in old.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')} == {k: v for k, v in new.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')}
a, z = old['current_work_snapshot'], new['current_work_snapshot']
keys = sorted(k for k in set(a) | set(z) if a.get(k) != z.get(k))
assert keys == record['changed_snapshot_keys']
assert not z['user_pause_requested'] and not z['paused_unfinished_task_indices'] and not z['pending_terminal_intakes_20261021']
assert (new['newAccepted'], new['target'], new['remaining'], new['latestAcceptance']) == (19, 20, 1, 'R041')
assert new['tasks'][637]['parent_disposition'] == 'FULL_SCOPE_PASS_TECHNICAL_CLOSED'
for i in [625, 627, 630, 631]:
    assert new['tasks'][i]['parent_disposition'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED'
assert new['tasks'][646:648] == old['tasks'][646:648]
for foreign in z['t3_recorded_running_different_owner']:
    assert not foreign['current_liveness_verified_here']
    assert foreign['current_thread_status_request'] == 'task_not_found_different_owner'
raw = json.loads((O / 'arithmetic-r160-dispatch.json').read_bytes())
r = raw['structuredContent']
request = json.loads((O / 'private/submitted-prompt.json').read_bytes())
assert (r['status'], r['workState'], r['providerInstanceId'], r['model']) == ('running', 'working', 'codex', 'gpt-6-astra')
assert {x['id']: x['value'] for x in r['options']} == request['target']['options'] == {'reasoningEffort': 'high', 'serviceTier': 'default'}
assert not r['hasPendingChildRuns'] and not r['hasPendingQuestion'] and r['pendingApproval'] is None
assert z['t3_current_confirmed_running'] == [r['taskId']]
assert z['t3_dispatch_observations'][:-1] == a['t3_dispatch_observations']
assert new['tasks'][648]['taskId'] == r['taskId'] and not new['tasks'][648]['accepted'] and new['tasks'][648]['count_change'] == 0
iso = json.loads((O / 'prospective-isolation.json').read_bytes())
brief = (P / iso['new_brief']['path']).read_bytes()
assert brief.decode() == request['task'] and sha(brief) == iso['new_brief']['sha256'] and len(brief) == iso['new_brief']['bytes']
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = brief.split(marker, 1)[1]
assert len(suffix) == 5570
for peer in iso['existing_peer_original_initial_briefs']:
    data = (P / peer['brief']).read_bytes()
    assert sha(data) == peer['sha256'] and b'*arithmetic*r160*' in data
    assert data.split(marker, 1)[1] == suffix
assert b'*arithmetic*r159*' in brief and b'*structural*r192*' in brief
tree_bytes = (P / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_bytes) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_bytes)
assert len(tree['tree']) == 13223 and not tree['truncated']
nav = json.loads((O / 'private/source062-navigation.json').read_bytes())
folder = 'preprints/Contact-Fano-manifolds-and-the-LeBrun-Salamon-conjecture-September-23-2026'
assert len([x for x in tree['tree'] if x['path'] == folder and x['type'] == 'tree']) == 1
entries = [x for x in tree['tree'] if x['path'].startswith(folder + '/')]
assert entries == nav['entries'] and len(entries) == 17 and sum(x['type'] == 'blob' for x in entries) == 14
assert not nav['parent_read_source_proofs']
selection = json.loads((O / 'private/source062-selection.json').read_bytes())
start, end = selection['catalogue_extent']
with (P / 'sources/CONTENTS.md').open('rb') as f:
    f.seek(start)
    selected = f.read(end - start)
assert selected == (O / 'private/catalogue-062.md').read_bytes()
assert sha(selected) == selection['selected_sha256'] and selection['family'] == 62 and selection['one_developed_family']
old_journal = original('frontier/NEW-TEN-2026-10-14.md')
assert len(old_journal) == base['journal_bytes'] and sha(old_journal) == base['journal_sha256']
assert (P / 'frontier/NEW-TEN-2026-10-14.md').read_bytes() == old_journal + (O / 'private/journal-append.bin').read_bytes()
for path, expected in base['protected_unrelated_sha256'].items():
    assert sha((P / path).read_bytes()) == expected
expected_names = {'openai-proof-research/' + x for x in allow}
assert len(expected_names) == len(allow)
assert not any('/private/' in x for x in allow)
assert not any('/fresh-arithmetic-discovery-r160/' in x for x in allow)
for path in allow:
    assert (P / path).is_file()
if '--staged' in sys.argv or committed:
    names = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines()) if committed else set(git('diff', '--cached', '--name-only').decode().splitlines())
    assert names == expected_names, (sorted(names - expected_names), sorted(expected_names - names))
    for path in allow:
        indexed = git('show', ('HEAD:' if committed else ':') + 'openai-proof-research/' + path)
        assert indexed == (P / path).read_bytes(), path
tracked_diff = set(git('diff', '--name-only').decode().splitlines())
expected_diff = {'openai-proof-research/' + x for x in base['protected_unrelated_sha256']}
if '--staged' not in sys.argv and not committed:
    expected_diff |= {'openai-proof-research/frontier/campaigns/2026-10-14/tasks.json', 'openai-proof-research/frontier/NEW-TEN-2026-10-14.md'}
assert tracked_diff == expected_diff, sorted(tracked_diff ^ expected_diff)
print(json.dumps({'result': 'MATCH', 'tasks': 649, 'new_task_index': 648, 'old_tasks_unchanged': 648, 'source_metadata_entries': 17, 'source_blobs': 14, 'standing_suffix_bytes': 5570, 'stage_allowlist_files': len(allow), 'count': '19/20', 'new_mathematical_gates': 0, 'foreign_liveness_verified': False, 'mode': 'committed' if committed else 'staged' if '--staged' in sys.argv else 'working'}))
