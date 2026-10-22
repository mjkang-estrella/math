"""Read-only bounded intake, scope, rights and coordination checks."""
from pathlib import Path
import hashlib
import json
import stat
import subprocess
import sys

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
O = Path(__file__).resolve().parent
A = B / 'fresh-arithmetic-discovery-r160'
base = json.loads((O / 'integration-baseline.json').read_bytes())
allow = json.loads((O / 'stage-allowlist.json').read_bytes())

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=P)

def original(path):
    return git('show', base['head'] + ':openai-proof-research/' + path)

committed = '--committed' in sys.argv
assert git('rev-parse', 'HEAD^' if committed else 'HEAD').decode().strip() == base['head']
old_bytes = original('frontier/campaigns/2026-10-14/tasks.json')
assert sha(old_bytes) == base['tasks_sha256']
old, new = json.loads(old_bytes), json.loads((B / 'tasks.json').read_bytes())
assert len(old['tasks']) == 649 and len(new['tasks']) == 650
assert old['tasks'][:648] == new['tasks'][:648]
assert old['tasks'][646:648] == new['tasks'][646:648]
changes = json.loads((O / 'integration-changes.json').read_bytes())
assert [i for i in range(649) if old['tasks'][i] != new['tasks'][i]] == changes['changed_old_task_indices'] == [648]
assert {k: v for k, v in old.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')} == {k: v for k, v in new.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')}
before, after = old['current_work_snapshot'], new['current_work_snapshot']
assert sorted(k for k in set(before) | set(after) if before.get(k) != after.get(k)) == changes['changed_snapshot_keys']
assert after['t3_recorded_running_different_owner'] == before['t3_recorded_running_different_owner']
assert (new['newAccepted'], new['target'], new['remaining'], new['latestAcceptance']) == (19, 20, 1, 'R041')
assert not after['user_pause_requested']
intake = json.loads((O / 'intake.json').read_bytes())
assert new['tasks'][648]['parent_disposition'] == intake['status'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED'
assert new['tasks'][648]['status'] == 'completed' and not new['tasks'][648]['parent_full_intake_pending']
assert not new['tasks'][648]['accepted'] and new['tasks'][648]['count_change'] == 0
assert sha((O / 'assessment.md').read_bytes()) == intake['assessment_sha256'] == new['tasks'][648]['parent_assessment_sha256']
assert intake['correctness_review'] == intake['contribution_review'] == 'NOT_STARTED_NO_NOMINEE'
assert intake['downstream'] == 'NOT_STARTED_NO_NOMINEE' and intake['publication'] == 'STOPPED'
for relative, expected in intake['outside_anchors'].items():
    assert sha((A / relative).read_bytes()) == expected
root = {x.relative_to(A).as_posix(): {'bytes': x.stat().st_size, 'sha256': sha(x.read_bytes()), 'mode': stat.S_IMODE(x.stat().st_mode)} for x in A.rglob('*') if x.is_file()}
assert not any(x.is_symlink() for x in A.rglob('*'))
assert root == json.loads((O / 'private/root-baseline.json').read_bytes()) and len(root) == 76
manifest = json.loads((A / 'MANIFEST.json').read_bytes())
assert len(manifest['files']) == manifest['file_count'] == 67
assert sum(x['bytes'] for x in manifest['files']) == manifest['total_bytes'] == 5369905
assert {x['path'] for x in manifest['files']} == {x for x in root if x.startswith('packet/')}
for row in manifest['files']:
    assert root[row['path']] == {k: row[k] for k in ('bytes', 'sha256', 'mode')}
assert json.loads((O / 'artifact-verification.json').read_bytes())['exit'] == 0
replay = json.loads((O / 'calculation-replay.json').read_bytes())
assert replay['exit'] == 0 and replay['saved_values_matched'] and not replay['mathematical_gate']
assert json.loads(replay['stdout']) == json.loads((A / 'packet/notes/calculation-values.json').read_bytes())
raw = json.loads((O / 'arithmetic-r161-dispatch.json').read_bytes())
r = raw['structuredContent']
request = json.loads((O / 'private/submitted-prompt.json').read_bytes())
assert not raw.get('isError') and (r['status'], r['workState'], r['providerInstanceId'], r['model']) == ('running', 'working', 'codex', 'gpt-6-astra')
assert {x['id']: x['value'] for x in r['options']} == request['target']['options'] == {'reasoningEffort': 'high', 'serviceTier': 'default'}
assert not r['hasPendingChildRuns'] and not r['hasPendingQuestion'] and r['pendingApproval'] is None
assert new['tasks'][649]['taskId'] == r['taskId'] and not new['tasks'][649]['accepted'] and new['tasks'][649]['count_change'] == 0
assert after['t3_current_confirmed_running'] == [r['taskId']]
assert after['t3_dispatch_observations'][:-1] == before['t3_dispatch_observations']
iso = json.loads((O / 'prospective-isolation-arithmetic161.json').read_bytes())
brief = (P / iso['new_brief']['path']).read_bytes()
assert brief.decode() == request['task'] and sha(brief) == iso['new_brief']['sha256'] and len(brief) == iso['new_brief']['bytes']
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = brief.split(marker, 1)[1]
assert len(suffix) == 5570
for peer in iso['existing_peer_original_initial_briefs']:
    data = (P / peer['brief']).read_bytes()
    assert sha(data) == peer['sha256'] and b'*arithmetic*r161*' in data
    assert data.split(marker, 1)[1] == suffix
assert b'*arithmetic*r159*' in brief and b'*structural*r192*' in brief and b'full-project-relative POSIX path.casefold()' in brief
tree_bytes = (P / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_bytes) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_bytes)
assert len(tree['tree']) == 13223 and not tree['truncated']
nav = json.loads((O / 'private/source063-navigation.json').read_bytes())
folder = 'preprints/The-Generalized-Mukai-Conjecture-September-24-2026'
entries = [x for x in tree['tree'] if x['path'].startswith(folder + '/')]
assert entries == nav['entries'] and len(entries) == 12 and sum(x['type'] == 'blob' for x in entries) == 10
assert not nav['parent_read_source_proofs']
selection = json.loads((O / 'private/source063-selection.json').read_bytes())
start, end = selection['catalogue_extent']
with (P / 'sources/CONTENTS.md').open('rb') as f:
    f.seek(start)
    selected = f.read(end - start)
assert selected == (O / 'private/catalogue-063.md').read_bytes() and sha(selected) == selection['selected_sha256']
old_journal = original('frontier/NEW-TEN-2026-10-14.md')
assert sha(old_journal) == base['journal_sha256'] and len(old_journal) == base['journal_bytes']
assert (P / 'frontier/NEW-TEN-2026-10-14.md').read_bytes() == old_journal + (O / 'private/journal-append.bin').read_bytes()
for relative, expected in base['protected_unrelated_sha256'].items():
    assert sha((P / relative).read_bytes()) == expected
expected_names = {'openai-proof-research/' + x for x in allow}
assert len(expected_names) == len(allow)
assert not any('/private/' in x or '/controls/' in x or x.endswith('/MANIFEST.json') for x in allow)
assert not any('/fresh-arithmetic-discovery-r161/' in x for x in allow)
for path in allow:
    assert (P / path).is_file()
if '--staged' in sys.argv or committed:
    names = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines()) if committed else set(git('diff', '--cached', '--name-only').decode().splitlines())
    assert names == expected_names, (sorted(names - expected_names), sorted(expected_names - names))
    for relative in allow:
        assert git('show', ('HEAD:' if committed else ':') + 'openai-proof-research/' + relative) == (P / relative).read_bytes()
expected_diff = {'openai-proof-research/' + x for x in base['protected_unrelated_sha256']}
if '--staged' not in sys.argv and not committed:
    expected_diff |= {'openai-proof-research/frontier/campaigns/2026-10-14/tasks.json', 'openai-proof-research/frontier/NEW-TEN-2026-10-14.md'}
assert set(git('diff', '--name-only').decode().splitlines()) == expected_diff
print(json.dumps({'result': 'MATCH', 'old_task_changes': [648], 'new_task': 649, 'tasks': 650, 'packet_files': 67, 'root_files_unchanged': 76, 'source063_descendants': 12, 'source063_blobs': 10, 'standing_suffix_bytes': 5570, 'accepted': '19/20', 'count_change': 0, 'foreign_records_preserved': True, 'staged_allowlist_files': len(allow), 'mode': 'committed' if committed else 'staged' if '--staged' in sys.argv else 'working'}))
