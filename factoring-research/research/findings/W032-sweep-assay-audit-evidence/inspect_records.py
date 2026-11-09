"""Audit bytes and existing record structure; NEVER import/execute assay code.

No candidate arithmetic is replayed: no prime/gcd/inverse/power/polynomial,
quotient, weight, threshold or carry is recalculated. Allowed calculations
are file hashes, counts, recorded-width metadata and interval coverage.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json

ROOT = Path('/home/mj-kang/Documents/Dev/math/factoring-research')
OUT = ROOT / 'research/findings/W032-sweep-assay-audit-evidence'
FROZEN = OUT / 'inputs'
REL = Path('research/findings/W032-lift-sweep-assay-evidence')
ASSAY = FROZEN / REL
failures = []
checks = []

def check(label, condition):
    checks.append({'check': label, 'passed': bool(condition)})
    if not condition:
        failures.append(label)

def read_json(path):
    return json.loads(path.read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def payload_check(manifest, base):
    rows = []
    for entry in manifest['files']:
        path = base / entry['path']
        rows.append({'path': entry['path'],
                     'bytes_match': path.stat().st_size == entry['bytes'],
                     'sha256_match': sha(path) == entry['sha256']})
    return rows

delivery_anchor = '0e0b4a6d60165794ccc1921d30ba3a7f753d5188c1e27bcf023618744eef272f'
freeze_anchor = '8b7387c453d5824d3948d11d9f161c49c6eb64ce67673c5e6e033a3d604a305c'
delivery = read_json(ASSAY / 'delivery-manifest.json')
freeze = read_json(ASSAY / 'freeze-manifest.json')
delivery_rows = payload_check(delivery, FROZEN)
freeze_rows = payload_check(freeze, ASSAY)
check('external delivery anchor', sha(ASSAY / 'delivery-manifest.json') == delivery_anchor)
check('external freeze anchor', sha(ASSAY / 'freeze-manifest.json') == freeze_anchor)
check('35 delivery entries', len(delivery_rows) == 35)
check('23 freeze entries', len(freeze_rows) == 23)
check('all delivery bytes and hashes', all(r['bytes_match'] and r['sha256_match'] for r in delivery_rows))
check('all freeze bytes and hashes', all(r['bytes_match'] and r['sha256_match'] for r in freeze_rows))
check('delivery sidecar', (ASSAY / 'terminal-manifest.sha256').read_text().split()[0] == delivery_anchor)
check('freeze sidecar', (ASSAY / 'freeze-manifest.sha256').read_text().split()[0] == freeze_anchor)
actual_delivery = {str(p.relative_to(FROZEN)) for p in ASSAY.rglob('*') if p.is_file()}
actual_delivery.add('research/findings/W032-lift-sweep-assay.md')
check('complete delivery file set and unique paths',
      actual_delivery == {r['path'] for r in delivery['files']} | set(delivery['exclusions'])
      and len({r['path'] for r in delivery['files']}) == 35)
check('unique freeze paths and freeze subset of delivery',
      len({r['path'] for r in freeze['files']}) == 23 and
      all(str(REL / r['path']) in actual_delivery for r in freeze['files']))
snapshot_checks = []
for row in read_json(OUT / 'input-manifest.json')['files']:
    path = ROOT / row['snapshot']
    snapshot_checks.append({'source': row['source'], 'bytes_match': path.stat().st_size == row['bytes'],
                            'sha256_match': sha(path) == row['sha256']})
check('all audit input snapshots unchanged', all(r['bytes_match'] and r['sha256_match'] for r in snapshot_checks))
for row in read_json(ASSAY / 'input-manifest.json')['inputs']:
    check('assay input snapshot ' + row['source'], sha(ASSAY / row['snapshot']) == row['sha256'] == row['live_sha256'])
for name in ['W032-lift-sweep-protocol.md', 'W032-lift-breakpoint-sweep.md']:
    check('current-frozen and assay-frozen target identical: ' + name,
          (FROZEN / 'research/findings' / name).read_bytes() ==
          (ASSAY / 'inputs/research/findings' / name).read_bytes())

source_lines = {name: len((ASSAY / name).read_text().splitlines())
                for name in ['assay.py', 'run_once.py', 'evidence_admin.py']}
check('complete source line counts', source_lines == {'assay.py': 562, 'run_once.py': 59, 'evidence_admin.py': 152})
events = [json.loads(line) for line in (ASSAY / 'events.jsonl').read_text().splitlines()]
records = [json.loads(line) for line in (ASSAY / 'records.jsonl').read_text().splitlines()]
status = read_json(ASSAY / 'status.json')
ledger = read_json(ASSAY / 'ledger-audit.json')
runner = read_json(ASSAY / 'runner-status.json')
marker = read_json(ASSAY / 'RUN-ONCE.json')
config = read_json(ASSAY / 'config.json')
check('event ids 1 through 20000 exactly', [e['id'] for e in events] == list(range(1, 20001)))
check('record count 1180', len(records) == 1180)
check('event clock nondecreasing', all(a['elapsed_s'] <= b['elapsed_s'] for a, b in zip(events, events[1:])))
check('record event counts and clocks nondecreasing',
      all(a['event_count'] <= b['event_count'] and a['elapsed_s'] <= b['elapsed_s'] for a, b in zip(records, records[1:])))
check('record event references in bounds', all(0 <= r['event_count'] <= len(events) for r in records))
check('event operands/results have correct recorded widths', all(
    e['operand_bits'] == [abs(x).bit_length() for x in e['operands']] and
    e['result_bits'] == [abs(x).bit_length() for x in (e['result'] if isinstance(e['result'], list) else [e['result']])]
    for e in events))
operations = dict(Counter(e['operation'] for e in events))
phases = dict(Counter(str(e['group']) + ':' + e['phase'] for e in events))
record_counts = dict(Counter(r['kind'] for r in records))
maximum_bits = max(max(e['operand_bits'] + e['result_bits']) for e in events)
check('operation summary matches status', operations == status['operations'])
check('phase summary matches status', phases == status['phases'])
check('record summary matches status and ledger', record_counts == status['record_counts'] == ledger['record_counts'])
check('maximum width matches status and ledger', maximum_bits == status['maximum_operand_or_result_bits'] == ledger['maximum_recorded_bits'] == 729)
check('event total matches status and ledger', len(events) == status['arithmetic_events'] == ledger['events'])
check('no failure records', 'primitive_failure' not in record_counts and 'traceback' not in status)
check('terminal status and freeze agree with runner', status['status'] == 'stopped_budget' and runner['status'] == 'child_finished' and runner['returncode'] == 2 and runner['freeze_manifest_sha256'] == freeze_anchor)
check('all runner frozen checks match independent byte inspection', all(r['matches'] for r in runner['freeze_checks']) and {r['path']: r['sha256'] for r in runner['freeze_checks']} == {r['path']: r['sha256'] for r in freeze['files']})
check('freeze precedes run marker', freeze['frozen_utc'] < marker['start_utc'])
check('runner and marker distinct child pid', runner['child_pid'] != marker['pid'])
check('empty stdout stderr', not (ASSAY / 'stdout.txt').read_bytes() and not (ASSAY / 'stderr.txt').read_bytes())
plans = [r for r in records if r['kind'] == 'group_plan']
check('exact three pre-arithmetic plans in frozen order', len(plans) == 3 and
      [p['planned']['b'] for p in plans] == config['groups_b'] == [9, 13, 17]
      and all(p['event_count'] == 0 and p['planned']['status'] == 'unstarted' for p in plans))
check('all events in fixed group order', [e['group'] for e in events] == [9] * 9330 + [13] * 9989 + [17] * 681)

metadata = {'kind', 'group', 'phase', 'event_count', 'elapsed_s'}
def content(record):
    return {k: v for k, v in record.items() if k not in metadata}

group_summaries = []
for group in status['groups']:
    b = group['b']
    label = 'b=' + str(b) + ': '
    rr = [r for r in records if r['group'] == b]
    ee = [e for e in events if e['group'] == b]
    ss = group['candidate']
    terminal = [r for r in rr if r['kind'] == 'group_terminal']
    check(label + 'exact terminal object equals status', len(terminal) == 1 and terminal[0]['result'] == group)
    check(label + 'event span equals count', group['end_event'] - group['start_event'] == len(ee))
    summary = {'b': b, 'status': group['status'], 'events': len(ee),
               'first_event': ee[0]['id'], 'last_event': ee[-1]['id'],
               'candidate_status': ss['status']}
    if group['status'] == 'complete':
        completed = [r for r in rr if r['kind'] == 'group_complete']
        check(label + 'complete object equals status', len(completed) == 1 and completed[0]['result'] == group)
        guards = [r['check'] for r in rr if r['kind'] == 'guard']
        check(label + 'guard records equal status', guards == ss['guards'])
        check(label + 'full denominator range retained', [g['value'] for g in guards if g['kind'] == 'denominator_factor'] == list(range(2, ss['m'] + 1)))
        check(label + 'every base index and initial guard retained', [g['i'] for g in guards if g['kind'] == 'initial_point'] == list(range(ss['m'] + 1)))
        check(label + 'all stored guards units', all(g['gcd'] == 1 and g['category'] == 'unit' for g in guards))
        for kind, key in [('base_point', 'base'), ('interval', 'intervals'), ('maximal_segment', 'maximal_segments'), ('tie_update', 'ties')]:
            check(label + kind + ' records equal status', [content(r) for r in rr if r['kind'] == kind] == ss[key])
        check(label + 'all coefficient records equal status', [r['value'] for r in rr if r['kind'] == 'coefficient'] == ss['coefficients'])
        thresholds = [r for r in rr if r['kind'] == 'threshold']
        check(label + 'retained threshold records equal status', [{k: v for k, v in content(r).items() if k != 'retained'} for r in thresholds if r['retained']] == ss['thresholds'])
        sr = [r for r in rr if r['kind'] == 'sorted_thresholds']
        check(label + 'sorted records equal status', len(sr) == 1 and sr[0]['thresholds'] == ss['sorted_thresholds'])
        check(label + 'sorting preserves threshold multiset', Counter(json.dumps(x, sort_keys=True) for x in ss['thresholds']) == Counter(json.dumps(x, sort_keys=True) for x in ss['sorted_thresholds']))
        check(label + 'stored thresholds nondecreasing', all(a['w'] <= z['w'] for a, z in zip(ss['sorted_thresholds'], ss['sorted_thresholds'][1:])))
        check(label + 'tie groups partition sorted thresholds', [event for tie in ss['ties'] for event in tie['events']] == ss['sorted_thresholds'])
        check(label + 'tie membership and distinct tie order', all(tie['events'] and all(e['w'] == tie['w'] for e in tie['events']) for tie in ss['ties']) and all(a['w'] < z['w'] for a, z in zip(ss['ties'], ss['ties'][1:])))
        ii = ss['intervals']
        n = group['N']
        check(label + 'interval coverage endpoints adjacency lengths', ii[0]['start'] == 0 and ii[-1]['end'] == n - 1 and
              all(v['start'] <= v['end'] and v['length'] == v['end'] - v['start'] + 1 for v in ii) and
              all(a['end'] + 1 == z['start'] for a, z in zip(ii, ii[1:])) and sum(v['length'] for v in ii) == n == ss['coverage'])
        check(label + 'interval boundaries match all ties', [v['start'] for v in ii[1:]] == [t['w'] for t in ss['ties']])
        check(label + 'tie old/new values link adjacent interval records', all(t['old_c'] == ii[i]['c'] and t['new_c'] == ii[i + 1]['c'] for i, t in enumerate(ss['ties'])))
        check(label + 'tie updates link recorded subtract events', all(events[r['event_count'] - 1]['operation'] == 'subtract' and
              events[r['event_count'] - 1]['operands'] == [r['old_c'], r['total_weight']] and
              events[r['event_count'] - 1]['result'] == r['new_c'] for r in rr if r['kind'] == 'tie_update'))
        check(label + 'interval gcds link recorded gcd events', all(any(e['operation'] == 'gcd' and e['operands'] == [r['c'], n] and e['result'] == r['gcd'] for e in events[max(0, r['event_count'] - 5):r['event_count']]) for r in rr if r['kind'] == 'interval'))
        check(label + 'stored all-unit outcomes', all(v['c'] != 0 and v['gcd'] == 1 and v['category'] == 'unit' for v in ii))
        cats = {cat: sum(v['length'] for v in ii if v['category'] == cat) for cat in ss['category_lengths']}
        check(label + 'category coverage and zero proper probability', cats == ss['category_lengths'] and ss['proper_length'] == 0 and ss['probability'] == {'numerator': 0, 'denominator': 1})
        check(label + 'distinct stored carry counts and width', len({v['c'] for v in ii}) == ss['distinct_c_count'] and max(abs(v['c']).bit_length() for v in ii) == ss['max_c_bits'])
        check(label + 'no equal ties or zero-net updates; segments identical to intervals', all(len(t['events']) == 1 and t['total_weight'] != 0 for t in ss['ties']) and ss['maximal_segments'] == ii and all(a['c'] != z['c'] for a, z in zip(ii, ii[1:])))
        controls = group['direct_controls']
        check(label + 'four labels as configured', [c['label'] for c in controls] == config['direct_controls'])
        for ctrl in controls:
            cr = [r for r in rr if r['kind'] == 'direct_control_complete' and r['control']['label'] == ctrl['label']]
            cp = [r for r in rr if r['kind'] == 'direct_control_point' and r['label'] == ctrl['label']]
            check(label + 'direct control ' + ctrl['label'] + ' complete record and points', len(cr) == 1 and cr[0]['control'] == ctrl and ctrl['status'] == 'passed' and ctrl['quotient'] == ctrl['expected'] and
                  [{k: v for k, v in content(r).items() if k not in {'label', 'w'}} for r in cp] == ctrl['points'] and [p['i'] for p in ctrl['points']] == list(range(ss['m'] + 1)))
            check(label + 'direct control ' + ctrl['label'] + ' terminal metered equality', events[ctrl['end_event'] - 1]['operation'] == 'equal' and events[ctrl['end_event'] - 1]['operands'] == [ctrl['quotient'], ctrl['expected']] and events[ctrl['end_event'] - 1]['result'] is True)
        sc = group['scalar_control']
        if b == 9:
            scr = [r for r in rr if r['kind'] == 'scalar_control_complete']
            check(label + 'one scalar complete and point records', len(scr) == 1 and scr[0]['control'] == sc and sc['status'] == 'passed' and [content(r) for r in rr if r['kind'] == 'scalar_control_point'] == sc['points'] and [p['i'] for p in sc['points']] == list(range(ss['m'] + 1)))
            differences = [r for r in rr if r['kind'] == 'scalar_difference_level']
            check(label + 'scalar difference shapes and terminal value', [r['order'] for r in differences] == list(range(1, ss['m'] + 1)) and [len(r['values']) for r in differences] == list(range(ss['m'], 0, -1)) and differences[-1]['values'] == [sc['filtered_integer']])
            check(label + 'scalar sign equality recorded', events[sc['end_event'] - 1]['operation'] == 'equal' and events[sc['end_event'] - 1]['operands'] == [sc['filtered_mod_N'], sc['negative_c0_mod_N']] and events[sc['end_event'] - 1]['result'] is True)
            summary['scalar_control'] = {k: v for k, v in sc.items() if k not in {'points', 'big_modulus', 'output_modulus', 'U'}}
        else:
            check(label + 'scalar not scheduled and absent from records', sc['status'] == 'not_scheduled' and not any(r['kind'].startswith('scalar_') for r in rr))
        summary.update(N=n, p=group['p'], q=group['q'], R=ss['R'], c0=ss['c0'],
                       thresholds=len(ss['thresholds']), intervals=len(ii), maximal_segments=len(ss['maximal_segments']),
                       distinct_c=ss['distinct_c_count'], max_c_bits=ss['max_c_bits'], coverage=ss['coverage'],
                       category_lengths=cats, probability=ss['probability'],
                       direct_controls=[{k: v for k, v in c.items() if k not in {'points', 'numerator'}} for c in controls],
                       diagnostic_verification=group['diagnostic_verification'],
                       no_multiple_ties=True)
    else:
        check(label + 'setup stop without parameters', group['status'] == 'stopped_budget' and all(k not in group for k in ['p', 'q', 'N']) and 'R' not in ss)
        check(label + 'candidate and all four direct controls and verification explicitly unstarted', ss['status'] == 'unstarted' and all(c['status'] == 'unstarted' and 'reason' in c for c in group['direct_controls']) and group['diagnostic_verification']['status'] == 'unstarted' and group['scalar_control']['status'] == 'not_scheduled')
        check(label + 'only setup events; no candidate/control records', all(e['phase'] == 'diagnostic_prime_generation' for e in ee) and all(r['kind'] in {'prime_trial', 'group_terminal', 'run_terminal'} for r in rr))
        summary['terminal_group'] = group
    group_summaries.append(summary)

exact_adjacent = [(a, b) for a, b in zip(events, events[1:]) if a['operation'] == 'divmod' and b['operation'] == 'equal' and b['operands'] == [a['result'][1], 0]]
check('all exact-division remainder guards true (no quotient replay)', all(b['result'] is True and a['result'][1] == 0 for a, b in exact_adjacent))
terminal = [r for r in records if r['kind'] == 'run_terminal']
check('one final run terminal agrees', len(terminal) == 1 and terminal[0]['arithmetic_events'] == 20000 and terminal[0]['operations'] == operations and terminal[0]['phases'] == phases)

result = {'scope': 'All stored bytes read; all JSONL rows and full status parsed. Structural/coverage/count/metadata comparisons only, no assay primitive replay or imports.',
          'failures': failures, 'checks': checks, 'delivery_anchor': delivery_anchor,
          'freeze_anchor': freeze_anchor, 'delivery_checks': delivery_rows, 'freeze_checks': freeze_rows,
          'audit_snapshot_checks': snapshot_checks, 'source_lines': source_lines,
          'events': len(events), 'records': len(records), 'operations': operations, 'phases': phases,
          'record_counts': record_counts, 'maximum_bits': maximum_bits, 'groups': group_summaries,
          'recorded_exact_divisions_with_remainder_guards': len(exact_adjacent),
          'negative_numerator_exact_divisions': sum(a['operands'][0] < 0 for a, b in exact_adjacent),
          'last_setup_events': events[-8:]}
with (OUT / 'integrity-and-structure.json').open('x') as stream:
    json.dump(result, stream, indent=2)
    stream.write('\n')
print(json.dumps({'checks': len(checks), 'failures': failures, 'events': len(events), 'records': len(records),
                  'source_lines': source_lines, 'operations': operations, 'phases': phases,
                  'groups': group_summaries, 'exact_division_guards': len(exact_adjacent),
                  'negative_numerator_exact_divisions': result['negative_numerator_exact_divisions'],
                  'last_setup_events': result['last_setup_events']}, indent=2))
