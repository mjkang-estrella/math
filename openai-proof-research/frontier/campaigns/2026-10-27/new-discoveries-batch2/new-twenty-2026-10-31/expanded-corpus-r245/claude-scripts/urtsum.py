"""Summarise URT test outputs (read-only)."""
import glob
import json
import os
import sys

d = sys.argv[1]
pat = sys.argv[2] if len(sys.argv) > 2 else 'test-*.json'
for p in sorted(glob.glob(os.path.join(d, pat))):
    rows = json.load(open(p))
    n = len(rows)
    viol = [r for r in rows if r['violations']]
    inc = [r['idx'] for r in rows if not r['complete']]
    multi = sum(r.get('multi_rect_tableaux', 0) for r in rows)
    checked = sum(r['checked_tableaux'] for r in rows)
    sizes = sorted(set(r['size'] for r in rows))
    print(os.path.basename(p), 'posets', n, 'sizes', sizes, 'tableaux', checked, 'multi', multi,
          'incomplete', inc[:10], 'VIOLATIONS', len(viol))
    for r in viol[:3]:
        print('  ', json.dumps(r)[:1500])
