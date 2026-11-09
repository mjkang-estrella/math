"""Validate results.json: parses, exactly the 20 reserved IDs, each with outcome and review_depth (read-only)."""
import json
import sys

lane = sys.argv[1]
r = json.load(open(lane + '/results.json'))
ids = json.load(open(lane + '/reservation.json'))['ids']
keys = sorted(int(k) for k in r['results'])
print('entries', len(keys), 'match reservation', keys == sorted(ids))
for k in ids:
    e = r['results'][str(k)]
    assert e.get('outcome') and e.get('review_depth'), k
print('outcomes:')
from collections import Counter
for o, c in Counter(e['outcome'] for e in r['results'].values()).most_common():
    print(' ', c, o)
