"""File-only freeze, ledger inspection and sealing. Never evaluates assay math."""
import ast
import collections
import hashlib
import json
from pathlib import Path
import platform
import sys
import time

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[2]
INPUTS = [
    'AGENTS.md', 'RESEARCH_TEAM.md', 'RESEARCH_LOOP.md', 'README.md', 'docs/SPECIFICATION.md',
    'research/STATE.md', 'research/hypotheses/W032.md',
    'research/findings/W032-lift-sweep-protocol.md',
    'research/findings/W032-lift-breakpoint-sweep.md',
    'research/findings/W032-exact-carry-quotient.md',
    'research/findings/W032-scalar-carry-review.md',
    'research/findings/W032-lift-control-review.md',
    'research/findings/W032-joint-lift-review.md',
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    with path.open('x') as out:
        json.dump(value, out, indent=2, sort_keys=True)
        out.write('\n')


def file_entry(path, relative_to):
    return dict(path=str(path.relative_to(relative_to)), bytes=path.stat().st_size, sha256=digest(path))


def freeze():
    if (ROOT / 'freeze-manifest.json').exists() or (ROOT / 'RUN-ONCE.json').exists():
        raise RuntimeError('freeze/run already exists; refusing a second freeze')
    snapshots = []
    for relative in INPUTS:
        source = PROJECT / relative
        target = ROOT / 'inputs' / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as out:
            out.write(source.read_bytes())
        snapshots.append(dict(source=relative, snapshot=str(target.relative_to(ROOT)),
                              sha256=digest(target), live_sha256=digest(source)))
    write_json(ROOT / 'input-manifest.json', dict(inputs=snapshots,
               note='File copies/hashes only; source interpretation is in read-scope.json.'))
    parsed = []
    for path in sorted(ROOT.glob('*.py')):
        ast.parse(path.read_text(), filename=str(path))
        parsed.append(file_entry(path, ROOT))
    write_json(ROOT / 'source-inspection.json', dict(
        syntax='passed ast.parse only; no assay import or evaluation', files=parsed,
        inspected='Meter wrappers, normalization, coefficient recurrence, stable threshold ordering, simultaneous ties, coverage, controls and terminal states.',
        parameter_changes=False, prefreeze_numerical_executions=0,
        code_review_scope='Single author source inspection; independent mathematical reviews remain separate.'))
    write_json(ROOT / 'environment.json', dict(python=sys.version, executable=sys.executable,
               implementation=platform.python_implementation(), platform=platform.platform(),
               dependencies='standard library only', compilation_or_tests='none; parent owns project checks'))
    files = [file_entry(path, ROOT) for path in sorted(ROOT.rglob('*')) if path.is_file()]
    manifest = dict(schema='W032-lift-sweep-freeze-v1',
                    frozen_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                    numerical_runs_before_freeze=0, files=files,
                    command='.venv/bin/python -B research/findings/W032-lift-sweep-assay-evidence/run_once.py',
                    exclusion='This manifest and its SHA-256 sidecar are necessarily excluded from their own payload list.')
    write_json(ROOT / 'freeze-manifest.json', manifest)
    sha = digest(ROOT / 'freeze-manifest.json')
    with (ROOT / 'freeze-manifest.sha256').open('x') as out:
        out.write(sha + '  freeze-manifest.json\n')
    print(json.dumps(dict(action='frozen', files=len(files), freeze_manifest_sha256=sha), sort_keys=True))


def audit():
    status = json.loads((ROOT / 'status.json').read_text())
    events = [json.loads(line) for line in (ROOT / 'events.jsonl').read_text().splitlines()]
    records = [json.loads(line) for line in (ROOT / 'records.jsonl').read_text().splitlines()]
    operations = collections.Counter(e['operation'] for e in events)
    phases = collections.Counter(str(e['group']) + ':' + e['phase'] for e in events)
    maximum_bits = max(max(e['operand_bits'] + e['result_bits']) for e in events)
    group_summaries = []
    for group in status['groups']:
        state = group['candidate']
        related = [r for r in records if r['group'] == group['b']]
        ties = [r for r in related if r['kind'] == 'tie_update']
        intervals = [r for r in related if r['kind'] == 'interval']
        group_events = [e for e in events if e['group'] == group['b']]
        group_summaries.append(dict(
            b=group['b'], status=group['status'], N=group.get('N'), p=group.get('p'), q=group.get('q'),
            R=state.get('R'), candidate_status=state['status'], c0=state.get('c0'),
            arithmetic_events=len(group_events), intervals=len(intervals),
            maximal_segments=len(state.get('maximal_segments', [])),
            distinct_c_count=state.get('distinct_c_count'), max_c_bits=state.get('max_c_bits'),
            recorded_category_lengths=state.get('category_lengths'),
            interval_categories=dict(collections.Counter(r['category'] for r in intervals)),
            coverage=state.get('coverage'), probability=state.get('probability'),
            direct_controls=[dict(label=c['label'], status=c['status'], w=c.get('w'),
                                  quotient=c.get('quotient'), expected=c.get('expected'),
                                  completed_points=len(c.get('points', []))) for c in group['direct_controls']],
            scalar_status=group['scalar_control']['status'],
            scalar_completed_points=len(group['scalar_control'].get('points', [])),
            proper_factor_records=state.get('factors', []),
            diagnostic_verification=group['diagnostic_verification'],
            retained_thresholds=len(state.get('thresholds', [])),
            tied_updates_with_multiple_events=sum(len(r['events']) > 1 for r in ties),
            zero_net_tied_updates=sum(r['total_weight'] == 0 for r in ties),
            last_recorded_interval=intervals[-1] if intervals else None,
            last_event=group_events[-1] if group_events else None))
    frozen = json.loads((ROOT / 'freeze-manifest.json').read_text())
    integrity = [dict(path=e['path'], matches=digest(ROOT / e['path']) == e['sha256'])
                 for e in frozen['files']]
    audit_result = dict(scope='Administrative ledger and frozen-byte inspection only; no arithmetic results replayed or assay functions imported.',
        events=len(events), contiguous_ids=[e['id'] for e in events] == list(range(1, len(events) + 1)),
        event_count_matches=len(events) == status['arithmetic_events'],
        operations_match=dict(operations) == status['operations'], phases_match=dict(phases) == status['phases'],
        maximum_recorded_bits=maximum_bits, maximum_bits_matches=maximum_bits == status['maximum_operand_or_result_bits'],
        records=len(records), record_counts=dict(collections.Counter(r['kind'] for r in records)),
        record_counts_match=dict(collections.Counter(r['kind'] for r in records)) == status['record_counts'],
        freeze_checks=integrity, all_frozen_files_unchanged=all(e['matches'] for e in integrity),
        groups=group_summaries)
    write_json(ROOT / 'ledger-audit.json', audit_result)
    print(json.dumps(audit_result, indent=2, sort_keys=True))


def seal():
    report = PROJECT / 'research/findings/W032-lift-sweep-assay.md'
    if not report.is_file():
        raise RuntimeError('report must exist before sealing')
    excluded = {'delivery-manifest.json', 'terminal-manifest.sha256'}
    files = [report] + [p for p in sorted(ROOT.rglob('*')) if p.is_file() and p.name not in excluded]
    manifest = dict(schema='W032-lift-sweep-delivery-v1',
        sealed_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
        project_root=str(PROJECT), files=[file_entry(p, PROJECT) for p in files],
        exclusions=[str((ROOT / p).relative_to(PROJECT)) for p in sorted(excluded)],
        note='Complete owned report/evidence payload. Self-manifest excluded; terminal sidecar and external handoff anchor its exact bytes. No payload edits after this seal.')
    write_json(ROOT / 'delivery-manifest.json', manifest)
    sha = digest(ROOT / 'delivery-manifest.json')
    with (ROOT / 'terminal-manifest.sha256').open('x') as out:
        out.write(sha + '  delivery-manifest.json\n')
    for entry in manifest['files']:
        if digest(PROJECT / entry['path']) != entry['sha256']:
            raise RuntimeError('delivery payload changed while sealing: ' + entry['path'])
    print(json.dumps(dict(action='sealed', payloads=len(files), delivery_manifest_sha256=sha,
                         all_payload_hashes_verified=True), sort_keys=True))


if __name__ == '__main__':
    {'freeze': freeze, 'audit': audit, 'seal': seal}[sys.argv[1]]()
