#!/usr/bin/env python3
"""r27 postcheck: rehash every receipt-recorded artifact against disk."""
import json, hashlib, os

def sha(p):
    with open(p, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()

SRC = 'src/CrownVGreedyNormalize.lean'
OLEAN = 'build/CrownVGreedyNormalize.olean'
AUDIT = 'audit/CrownVGreedyNormalizeAxioms.lean'

receipts = {}
by_label = {}
for fn in sorted(os.listdir('receipt')):
    r = json.load(open('receipt/' + fn))
    ok = True
    for key, pathfield in (('source_sha256', 'source'),
                           ('target_olean_sha256', 'target_olean'),
                           ('log_sha256', 'log')):
        if r.get(key):
            ok = ok and r[key] == sha(r[pathfield])
    receipts[fn] = {'sha256': sha('receipt/' + fn), 'exit': r['exit'],
                    'label': r['label'],
                    'pinned_source_olean_log_match': ok}
    by_label.setdefault(r['label'], []).append((fn, r['exit']))

def seal_fn(label):
    cands = [fn for fn, e in by_label[label] if e == 0]
    assert len(cands) == 1, label
    return cands[0]

fn_strict = seal_fn('lean_CrownVGreedyNormalize')
fn_check = seal_fn('leanchecker_CrownVGreedyNormalize')
fn_ax = seal_fn('axioms_CrownVGreedyNormalize')

seal = json.load(open('receipt/' + fn_strict))
assert seal['source_sha256'] == sha(SRC), 'sealed source hash drift'
assert seal['target_olean_sha256'] == sha(OLEAN), 'sealed olean hash drift'
axr = json.load(open('receipt/' + fn_ax))
assert axr['source_sha256'] == sha(AUDIT), 'audit hash drift'

all_ok = (receipts[fn_strict]['pinned_source_olean_log_match'] and
          receipts[fn_check]['pinned_source_olean_log_match'] and
          receipts[fn_ax]['pinned_source_olean_log_match'] and
          receipts[fn_strict]['exit'] == 0 and
          receipts[fn_check]['exit'] == 0 and
          receipts[fn_ax]['exit'] == 0)
failed = [k for k, v in receipts.items() if v['exit'] != 0]
post = {'receipts': receipts,
        'source': sha(SRC),
        'olean': sha(OLEAN),
        'audit': sha(AUDIT),
        'sealed_strict_receipt': fn_strict,
        'sealed_checker_receipt': fn_check,
        'sealed_axioms_receipt': fn_ax,
        'failed_attempt_receipts_diagnostic_history': failed,
        'all_pinned_hashes_match': all_ok}
json.dump(post, open('postcheck.json', 'w'), indent=1)
for k, v in sorted(receipts.items()):
    print(v['label'], v['exit'], v['pinned_source_olean_log_match'], v['sha256'][:16])
print('source', post['source'])
print('olean', post['olean'])
print('all_pinned_hashes_match', all_ok)
