"""Read-only scope, byte-integrity and explicit staging checks."""
from pathlib import Path
import hashlib
import json
import stat
import subprocess
import sys

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
O = Path(__file__).resolve().parent
A = B / 'fresh-arithmetic-discovery-r161'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=P)

base = json.loads((O / 'integration-baseline.json').read_bytes())
allow = json.loads((O / 'stage-allowlist.json').read_bytes())
committed = '--committed' in sys.argv
assert git('rev-parse', 'HEAD^' if committed else 'HEAD').decode().strip() == base['head']
old_bytes = git('show', base['head'] + ':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json')
assert sha(old_bytes) == base['tasks_sha256']
old = json.loads(old_bytes)
new = json.loads((B / 'tasks.json').read_bytes())
changes = json.loads((O / 'integration-changes.json').read_bytes())
assert len(old['tasks']) == 651 and len(new['tasks']) == 652
assert [i for i in range(651) if old['tasks'][i] != new['tasks'][i]] == changes['changed_old_task_indices'] == [649]
assert old['tasks'][650] == new['tasks'][650]
assert old['tasks'][646:649] == new['tasks'][646:649]
assert {k: v for k, v in old.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')} == {k: v for k, v in new.items() if k not in ('tasks', 'last_parent_progress', 'current_work_snapshot')}
s, t = old['current_work_snapshot'], new['current_work_snapshot']
assert sorted(k for k in set(s) | set(t) if s.get(k) != t.get(k)) == changes['changed_snapshot_keys']
assert (new['newAccepted'], new['target'], new['remaining'], new['latestAcceptance']) == (19, 20, 1, 'R041')
assert not t['user_pause_requested']
intake = json.loads((O / 'intake.json').read_bytes())
assert new['tasks'][649]['parent_disposition'] == intake['status'] == 'PREFREEZE_NO_NOMINEE_ARCHIVED'
assert new['tasks'][649]['status'] == 'completed' and not new['tasks'][649]['parent_full_intake_pending']
assert not new['tasks'][649]['accepted'] and new['tasks'][649]['count_change'] == 0
assert sha((O / 'assessment.md').read_bytes()) == intake['assessment_sha256']
assert intake['correctness_review'] == intake['contribution_review'] == 'NOT_STARTED_NO_NOMINEE'
assert intake['downstream'] == 'NOT_STARTED_NO_NOMINEE' and intake['publication'] == 'STOPPED'
for relative, expected in intake['outside_anchors'].items():
    assert sha((A / relative).read_bytes()) == expected
root = {x.relative_to(A).as_posix(): {'bytes': x.stat().st_size, 'sha256': sha(x.read_bytes()), 'mode': stat.S_IMODE(x.stat().st_mode)} for x in A.rglob('*') if x.is_file()}
assert not any(x.is_symlink() for x in A.rglob('*'))
assert root == json.loads((O / 'private/root-baseline.json').read_bytes()) and len(root) == 85
m = json.loads((A / 'packet/MANIFEST.json').read_bytes())
assert m['file_count'] == len(m['files']) == 69 and m['total_bytes'] == sum(x['bytes'] for x in m['files']) == 3255120
assert {x['path'] for x in m['files']} == {x.removeprefix('packet/') for x in root if x.startswith('packet/') and x != 'packet/MANIFEST.json'}
for row in m['files']:
    observed = root['packet/' + row['path']]
    assert (observed['bytes'], observed['sha256']) == (row['bytes'], row['sha256'])
assert json.loads((O / 'artifact-verification.json').read_bytes())['exit'] == 0
assert json.loads((O / 'finite-checks.json').read_bytes())['all_checks_passed']
raw = json.loads((O / 'arithmetic-r162-dispatch.json').read_bytes())
r = raw['structuredContent']
request = json.loads((O / 'private/submitted-prompt.json').read_bytes())
assert not raw.get('isError') and (r['status'], r['workState'], r['providerInstanceId'], r['model']) == ('running', 'working', 'codex', 'gpt-6-astra')
assert {x['id']: x['value'] for x in r['options']} == request['target']['options'] == {'reasoningEffort': 'high', 'serviceTier': 'default'}
assert not r['hasPendingChildRuns'] and not r['hasPendingQuestion'] and r['pendingApproval'] is None
assert new['tasks'][651]['taskId'] == r['taskId'] and not new['tasks'][651]['accepted'] and new['tasks'][651]['count_change'] == 0
assert t['t3_current_confirmed_running'] == [r['taskId']]
assert t['t3_dispatch_observations'][:-1] == s['t3_dispatch_observations']
assert t['t3_recorded_running_different_owner'][0]['task_index'] == 650 and not t['t3_recorded_running_different_owner'][0]['current_liveness_verified_here']
iso = json.loads((O / 'prospective-isolation-arithmetic162.json').read_bytes())
brief = (P / iso['new_brief']['path']).read_bytes()
assert brief.decode() == request['task'] and sha(brief) == iso['new_brief']['sha256'] and len(brief) == iso['new_brief']['bytes']
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
suffix = brief.split(marker, 1)[1]
assert len(suffix) == 5570 and b'*t185144-*' in brief and b'*k369134-*' in brief
for peer in iso['existing_peer_original_initial_briefs']:
    data = (P / peer['brief']).read_bytes()
    assert sha(data) == peer['sha256'] and b'*arithmetic*r162*' in data
    assert data.split(marker, 1)[1] == suffix
tree_bytes = (P / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_bytes) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_bytes)
assert len(tree['tree']) == 13223 and not tree['truncated']
nav = json.loads((O / 'private/source064-navigation.json').read_bytes())
folder = 'preprints/Topological-triviality-of-mu-constant-families-of-surface-singularities-September-24-2026'
entries = [x for x in tree['tree'] if x['path'].startswith(folder + '/')]
assert entries == nav['entries'] and len(entries) == 24 and sum(x['type'] == 'blob' for x in entries) == 21
assert not nav['parent_read_source_proofs']
selection = json.loads((O / 'private/source064-selection.json').read_bytes())
start, end = selection['catalogue_extent']
with (P / 'sources/CONTENTS.md').open('rb') as f:
    f.seek(start)
    selected = f.read(end - start)
assert selected == (O / 'private/catalogue-064.md').read_bytes() and sha(selected) == selection['selected_sha256']
journal = git('show', base['head'] + ':openai-proof-research/frontier/NEW-TEN-2026-10-14.md')
assert sha(journal) == base['journal_sha256'] and len(journal) == base['journal_bytes']
assert (P / 'frontier/NEW-TEN-2026-10-14.md').read_bytes() == journal + (O / 'private/journal-append.bin').read_bytes()
for relative, expected in base['protected_unrelated_sha256'].items():
    assert sha((P / relative).read_bytes()) == expected
expected_names = {'openai-proof-research/' + x for x in allow}
assert len(expected_names) == len(allow)
assert not any('/private/' in x or '/tiny-controls/' in x or x.endswith('/MANIFEST.json') for x in allow)
assert not any('/fresh-arithmetic-discovery-r162/' in x for x in allow)
for relative in allow:
    assert (P / relative).is_file()
if '--staged' in sys.argv or committed:
    names = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines()) if committed else set(git('diff', '--cached', '--name-only').decode().splitlines())
    assert names == expected_names
    for relative in allow:
        assert git('show', ('HEAD:' if committed else ':') + 'openai-proof-research/' + relative) == (P / relative).read_bytes()
expected_diff = {'openai-proof-research/' + x for x in base['protected_unrelated_sha256']}
if '--staged' not in sys.argv and not committed:
    expected_diff |= {'openai-proof-research/frontier/campaigns/2026-10-14/tasks.json', 'openai-proof-research/frontier/NEW-TEN-2026-10-14.md'}
assert set(git('diff', '--name-only').decode().splitlines()) == expected_diff
print(json.dumps({'result': 'MATCH', 'changed_old_task_indices': [649], 'new_task': 651, 'tasks': 652, 'packet_files': 69, 'immutable_root_files': 85, 'source064_descendants': 24, 'source064_blobs': 21, 'standing_suffix_bytes': 5570, 'accepted': '19/20', 'count_change': 0, 'foreign_and_prior_archives_preserved': True, 'allowlist_files': len(allow), 'mode': 'committed' if committed else 'staged' if '--staged' in sys.argv else 'working'}))
