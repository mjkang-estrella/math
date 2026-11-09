import json
from pathlib import Path

base = Path(__file__).resolve().parent
items = json.loads((base / 'inventory.json').read_text())
proof_ids = {'333569', '365710', '372205', '356756', '365943', '353203', '338887', '343536'}
ledger = json.loads((base.parents[2] / 'frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json').read_text())
for item in items:
    item['status'] = 'pending_live_duplicate_check'
    if item['id'].startswith('D'):
        entry = next(e for e in ledger['accepted'] if e['number'] == int(item['id'][1:]))
        item['mapping_note'] = entry.get('mathdb_scope_note', 'No exact MathDB record established in the acceptance ledger.')
        item['source_target'] = entry['source_target']
        item['source_url'] = entry['source_url']
        if item['id'] == 'D31':
            item['problem_id'] = '325512'
            item['label'] = 'partial_progress'
            item['summary'] = 'The surviving 2019 parameter-concavity question is proved: for every x > 0, the generalized inverse hyperbolic sine is strictly concave in p > log(2)/2. This is narrower than the older all-p > 0 assertion in this record.'
        else:
            item['status'] = 'needs_exact_problem_mapping'
            continue
    else:
        item['problem_id'] = item['id']
        item['label'] = 'proof' if item['id'] in proof_ids else 'counterexample'
        if item['id'] == '354228':
            item['label'] = 'partial_progress'
        item['summary'] = item['title']
    assert len(item['summary']) <= 500
    item['body'] = ('**Result and scope.** ' + item['scope'] + '\n\n'
        + (item.get('mapping_note', '') + '\n\n' if item['id'].startswith('D') else '')
        + '**Complete proof:** [' + item['title'] + '](' + item['url'] + ') · '
        + '[PDF](' + item['url'].replace('/abs/', '/pdf/') + 'v1).\n\n'
        + 'The paper page contains the supplementary proof-source JSON and `extract_sources.py`. '
        + 'The linked paper supplies the complete argument and states the precise scope of the Lean certificate, '
        + 'ordinary proofs, supporting computations, and source interpretation. Those qualifications are retained here; '
        + 'a supporting computation is not a proof of a broader statement.\n\n'
        + 'This is an AI-assisted research preprint. Internal review is not external journal peer review. '
        + 'Bounded prior-art searches do not establish worldwide priority. See the paper for formalization and trust limits.')
(base / 'prepared-links.json').write_text(json.dumps(items, indent=2) + '\n')
print(json.dumps({'prepared': sum('body' in x for x in items), 'needs_mapping': [x['id'] for x in items if 'body' not in x]}))
