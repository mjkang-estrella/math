"""One-time arithmetic115 no-nominee archive and actual arithmetic116 dispatch."""
import datetime
import importlib.util
import json
from pathlib import Path

O = Path(__file__).resolve().parent
B = O.parent
P = B.parents[2]
spec = importlib.util.spec_from_file_location('a115_replay', O / 'replay.py')
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)


def read(p):
    return json.loads(p.read_text())


def dump(p, data):
    p.write_text(json.dumps(data, indent=2) + '\n')


now = datetime.datetime.now(datetime.timezone.utc).isoformat()
t = read(B / 'tasks.json')
assert len(t['tasks']) == 508
intake = {
    'observed_utc': now, 'disposition': 'PREFREEZE_NO_NOMINEE',
    'scope_frozen': False, 'nominee': None,
    'correctness': 'UNREVIEWED', 'contribution': 'UNREVIEWED',
    'assessment_sha256': h.sha(O / 'assessment.md'),
    'external_handoff_anchors': h.ANCHORS,
    'payload_files': 61, 'whole_root_files': 64, 'subdirectories': 21,
    'source_blobs': 20, 'primary_pdfs': 2,
    'stable_whole_original_copies': 10, 'mutable_original_excerpts': 2,
    'artifact_cases': 7, 'negative_cases': 5,
    'accepted': False, 'count_change': 0, 'publication': 'STOPPED',
}
dump(O / 'intake.json', intake)
r = read(O / 'task-status.json')['structuredContent']
assert r['status'] == 'completed' and not r['hasPendingChildRuns']
t['tasks'][506].update(r)
t['tasks'][506].update(
    parent_observed_terminal_utc=now,
    parent_disposition='PREFREEZE_NO_NOMINEE', scope_frozen=False,
    nominee=None, correctness='UNREVIEWED', contribution='UNREVIEWED',
    parent_assessment='discovery-arithmetic-r115-parent/assessment.md',
    parent_intake='discovery-arithmetic-r115-parent/intake.json',
    accepted=False, count_change=0,
    status_provenance='Actual completed original task_status with detached anchors and parent artifact archive; no independent mathematical/contribution grade.',
)
d = read(O / 'r116-dispatch.json')['structuredContent']
assert d['status'] == 'running'
assert d['providerInstanceId'] == 'codex' and d['model'] == 'gpt-6-astra'
assert {e['id']: e['value'] for e in d['options']} == {
    'reasoningEffort': 'high', 'serviceTier': 'default'}
brief = 'expanded-target-2026-10-17/fresh-arithmetic-r116-brief.txt'
t['tasks'].append({
    'observed_utc': now,
    'target': {'providerInstanceId': 'codex', 'model': 'gpt-6-astra',
               'options': {'reasoningEffort': 'high', 'serviceTier': 'default'}},
    **d, 'role': 'research', 'output': 'fresh-arithmetic-discovery-r116',
    'brief': brief, 'brief_sha256': h.sha(B / brief),
    'parent_count_at_dispatch': 19, 'accepted': False, 'count_change': 0,
    'publication': 'STOPPED',
    'status_provenance': 'Actual async delegate_task response,not later liveness polling.',
})
msg = (
    'Arithmetic115 archived PREFREEZE/no nominee: one Source019 family retains '
    'every prime/finite p-adic field,all affine hyperbolic types,FULL groups/every '
    'section/geometric conjugacy/all rational cusp packets. Cofinal characteristic '
    'neighborhoods and exact Riemann-Hurwitz pay high-genus completions even in '
    'low-genus cases;stipulated proper Source019 points are functorially compatible. '
    'Actually read Tamagawa2.8(iv) local-field/inverse-limit argument and Stix '
    'Kummer/packet proofs pay one full decomposition group and whole cusp torsors. '
    'No newly unpaid affine bridge or nonroutine contribution is identified; '
    'no global/effective/topological strengthening is inferred. T019S59 full '
    'quotient-section scope/proof/historical conditional TECHNICAL remains unchanged. '
    'Reading bounds,initial navigation overrun,copied-TeX/ledger/helper false '
    'admissions,late alias reads and mutable excerpt limits are preserved. '
    'Parent checked 61 payloads+3 envelopes,21 subdirectories,20 canonical '
    'sources,2 primary PDFs,10 stable whole copies+2 excerpts,and 7 complete-copy '
    'controls with 5 negatives. No numerical/formal mathematical suite or grade. '
    'Arithmetic116 actually dispatched Astra high/default with full standing brief. '
    'Structural151 INITIAL brief already excludes116;Analytic145 isolation-only '
    'exclusion was STEERED into the same original running ordinal1 before116 '
    'brief/root creation,verified by exact thread/run against prestatus;optional '
    'taskId was absent,no duplicate send/new followup task. New116 excludes '
    'both peers and future152/146.19/20/latestR041,one remains;publication STOPPED.'
)
t['last_parent_progress'] = {
    'observed_utc': now, 'note': msg, 'newAccepted': 19,
    'remaining': 1, 'publication': 'STOPPED'}
s = t['current_work_snapshot']
s.update(
    observed_utc=now, note=msg, status_note=msg,
    fresh_discovery_current=[t['tasks'][i]['output'] for i in [505, 507, 508]],
    t3_current_confirmed_running=[t['tasks'][i]['taskId'] for i in [505, 507, 508]],
)
s['t3_dispatch_observations'].append({
    'observed_utc': now, 'record': 'discovery-arithmetic-r115-parent/r116-dispatch.json', **d})
s['arithmetic_r115_archive'] = intake | {
    'assessment': 'discovery-arithmetic-r115-parent/assessment.md', 'taskId': r['taskId']}
s['arithmetic116_prospective_isolation'] = {
    'receipt': 'discovery-arithmetic-r115-parent/prospective-isolation.json',
    'structural151_initial_brief_excludes_future116': True,
    'analytic145_same_original_r1_isolation_steered_before116': True,
    'analytic145_presteer_status': 'discovery-arithmetic-r115-parent/analytic145-before-arithmetic116-status.json',
    'analytic145_actual_steer_receipt': 'discovery-arithmetic-r115-parent/analytic145-arithmetic116-isolation.json',
    'active_peers': ['fresh-structural-discovery-r151', 'fresh-analytic-discovery-r145'],
    'new116_initial_brief': brief, 'new116_initial_brief_sha256': h.sha(B / brief),
    'new116_initial_future_exclusions': ['*structural*r152*', '*analytic*r146*'],
    'liveness_polling': False,
}
dump(B / 'tasks.json', t)
with (P / 'frontier/NEW-TEN-2026-10-14.md').open('a') as f:
    f.write('\n\n## Parent update — arithmetic115 archive and arithmetic116 dispatch\n\n'
            + msg + ' See [parent assessment](campaigns/2026-10-14/discovery-arithmetic-r115-parent/assessment.md). No mathematical gate or acceptance assigned.\n')
root = B / 'fresh-arithmetic-discovery-r115'
original = ['FINAL.md', 'REPORT.md', 'MANIFEST.json',
            'packet/README.md', 'packet/READING.md',
            'packet/incoming-identities.json', 'packet/source-identities.json',
            'packet/notes/start.md', 'packet/notes/affine-reduction.md']
original += ['packet/tools/' + n for n in [
    'history_scan.py', 'acquire_source.py', 'late_alias_scan.py',
    'capture_inputs.py', 'verify.py', 'copied_controls.py', 'seal_once.py']]
metadata = ['packet/private/primary/identities.json',
            'packet/private/controls/receipt.json']
parent = [
    'assessment.md', 'replay.py', 'integrate.py', 'integration-check.py',
    'integration-baseline.json', 'integration-validation.json',
    'observed-root.json', 'copied-controls.json', 'input-authentication.json',
    'replay.json', 'intake.json', 'task-status.json', 'capabilities.json',
    'r116-dispatch.json', 'prospective-isolation.json', 'staging-allowlist.json',
    'analytic145-before-arithmetic116-status.json',
    'analytic145-arithmetic116-isolation.json',
]
files = [str((root / n).relative_to(P)) for n in original + metadata]
files += [str((O / n).relative_to(P)) for n in parent]
files += [str((B / brief).relative_to(P)), str((B / 'tasks.json').relative_to(P)),
          'frontier/NEW-TEN-2026-10-14.md']
dump(O / 'staging-allowlist.json', {
    'files': files, 'private_metadata_only': metadata,
    'limits': 'Original public prose/code and two named private metadata records only; no protected source/primary/history/search/render or copied fixture bodies.',
})
