"""Read stored terminal envelopes after the structural audit flagged them.

This is a further record inspection, never an assay run or arithmetic replay.
The original failing checks and original evidence are preserved unchanged.
"""
from pathlib import Path
import json

ROOT = Path('/home/mj-kang/Documents/Dev/math/factoring-research')
OUT = ROOT / 'research/findings/W032-sweep-assay-audit-evidence'
ASSAY = OUT / 'inputs/research/findings/W032-lift-sweep-assay-evidence'
records = [json.loads(line) for line in (ASSAY / 'records.jsonl').read_text().splitlines()]
status = json.loads((ASSAY / 'status.json').read_text())
terminal = [(i + 1, r) for i, r in enumerate(records) if r['kind'] == 'group_terminal']
summaries = []
for line, record in terminal:
    b = record['result']['b']
    matches = [g for g in status['groups'] if g['b'] == b]
    summaries.append({'record_line': line, 'envelope_group': record['group'],
                      'envelope_phase': record['phase'], 'event_count': record['event_count'],
                      'payload_group': b, 'payload_status': record['result']['status'],
                      'payload_equals_status': len(matches) == 1 and matches[0] == record['result'],
                      'envelope_matches_payload_group': record['group'] == b})
result = {'scope': 'Stored-record equality and attribution only. No mutation or candidate replay.',
          'terminal_records': summaries,
          'all_planned_terminal_payloads_retained': [r['payload_group'] for r in summaries] == [9, 13, 17],
          'all_payloads_equal_status': all(r['payload_equals_status'] for r in summaries),
          'source_cause': 'assay.py:550-551 iterates group objects but does not reset meter.group or meter.phase; Meter.record:47-48 writes the active group/phase.',
          'impact': 'Two terminal envelopes misattribute completed groups to b=17. Nested results and status.json retain each exact group outcome. Arithmetic event accounting is unaffected. Preserve and disclose, do not repair or rerun.'}
with (OUT / 'terminal-attribution.json').open('x') as stream:
    json.dump(result, stream, indent=2)
    stream.write('\n')
print(json.dumps(result, indent=2))
