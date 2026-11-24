#!/usr/bin/env python3
"""Fresh pools for the tier-1 proof pass (root Claude Fable 5.2, 2026-11-20).
Records never assigned to any lane, ranked by the routing score of
root-intake-r60/build-fresh-shards-20261120.py, 30 per pool, pools 049 onward.
Run from C:  python3 -I public-claim-100/scripts/build_fresh_pools.py [N_POOLS] [--dry]
"""
import json, glob, re, sys, random, collections
NP = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 26
src = open('root-intake-r60/build-fresh-shards-20261120.py').read()
good = eval(re.search(r'^good=(\{.*\})$', src, re.M).group(1))
bad = eval(re.search(r'^bad=(\{.*\})$', src, re.M).group(1))
touched = set(json.load(open('root-intake-r60/touched-ids-superset-20261118-v2.json')))
for f in glob.glob('root-intake-r60/fresh-shards-2026111[89]/shard-*.json') + glob.glob('root-intake-r60/fresh-shards-20261120/shard-*.json'):
    touched |= {r['mathdb_id'] for r in json.load(open(f))['rows']}
touched |= {int(x) for x in open('public-claim-100/principia-ids.txt').read().split() if x.strip().isdigit()}
L = json.load(open('ledger.json'))
touched |= {a['mathdb_id'] for a in L['accepted'] if a.get('mathdb_id')}
touched |= {int(k) for k in L['excluded_after_review']}
for f in glob.glob('public-claim-100/t1-pools/pool-*.json'):
    touched |= {e['mathdb_id'] for e in json.load(open(f))['entries']}
touched |= {int(k) for k in json.load(open('public-claim-100/LANES.json'))['candidates'] if k.isdigit()}
rows = []
for f in sorted(glob.glob('../lanes/pi-mathdb-full-corpus-inventory-r301/corpus/*.jsonl')):
    for line in open(f, encoding='utf-8'):
        if line.strip(): rows.append(json.loads(line))
cand = []
for r in rows:
    i = r['mathdb_id']
    if i in touched or r.get('status') != 'open' or r.get('statement_completeness') != 'full' or r.get('solution_count') or r.get('post_type') not in ('conjecture', 'open_problem'): continue
    if r.get('importance') != 'corpus': continue
    tags = r.get('tags') or []; st = r.get('statement') or ''
    s = sum(good.get(t, 0) for t in tags) - 4 * sum(t in bad for t in tags)
    y = r.get('first_stated_year') or 0
    if y >= 2022: s += 3
    elif y >= 2017: s += 2
    elif y >= 2008: s += 1
    elif 0 < y < 1990: s -= 3
    if 'arxiv.org' in (r.get('source_url') or ''): s += 1
    n = len(st)
    if 250 < n < 1600: s += 1
    if n > 2500: s -= 2
    low = st.lower()
    if re.search(r'for (all|every|each) (positive |nonnegative )?integers?|\\binom|\\sum|\\prod|\\le|\\ge|\\equiv', st): s += 1
    if re.search(r'asymptotic|almost surely|with high probability|polynomial[- ]time|np-hard|there exists a constant|absolute constant', low): s -= 2
    if r.get('post_type') == 'conjecture': s += 1
    # proof-pass preference: a conjecture from an arXiv source, with an explicit quantified statement
    if s >= 6: cand.append((s, i, r))
print('untouched candidates', len(cand), sorted(collections.Counter(s for s, _, _ in cand).items()))
if '--dry' in sys.argv: sys.exit()
random.seed(2026112015)
by = collections.defaultdict(list)
for s, i, r in cand: by[s].append((s, i, r))
order = []
for s in sorted(by, reverse=True):
    random.shuffle(by[s]); order += by[s]
existing = sorted(glob.glob('public-claim-100/t1-pools/pool-*.json'))
n0 = max(int(re.search(r'pool-(\d+)', f).group(1)) for f in existing)
keep = ('title', 'post_type', 'tags', 'source_name', 'source_url', 'first_stated_year')
for k in range(NP):
    chunk = order[k * 30:(k + 1) * 30]
    if not chunk: break
    n = n0 + 1 + k
    json.dump({'pool': n, 'kind': 'fresh', 'note': 'Records never assigned to any lane in this campaign (retained corpus snapshot of 2026-08 to 2026-10, not live status). No earlier lane notes exist.',
               'entries': [{'mathdb_id': i, 'routing_score': s, **{f: r.get(f) for f in keep}, 'earlier': []} for s, i, r in chunk]},
              open(f'public-claim-100/t1-pools/pool-{n:03d}.json', 'w'), ensure_ascii=False, indent=1)
    print('pool', n, 'scores', collections.Counter(s for s, _, _ in chunk))
