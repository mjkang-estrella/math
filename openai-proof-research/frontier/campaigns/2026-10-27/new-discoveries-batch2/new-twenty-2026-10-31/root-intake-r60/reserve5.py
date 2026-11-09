# reserve5 (root, 2026-11-02): discrete conjectures whose MathDB statement cites computational verification
# (verified/checked/confirmed up to some size). These are the shape of the strongest recent leads (373367 failed just beyond
# the authors' verified range). Built on reserve4.
# Reuses reserve2.py eligibility and exclusions (via runpy, RESERVE_N=0), then restricts to rows whose
# corpus record has first_stated_year >= YEAR_FLOOR (default 2022), solution_count 0, and a
# discrete-mathematics keyword in MathDB tags or title. Cue-first lanes (r87) mostly hit known
# refutations of older conjectures; recent posing lowers that risk.
# Ranking: no hard_structural tag, few-parameter cue, elementary-inequality or identity cue,
# review score, newer year, then ID.
import os, sys, json, glob, datetime, runpy
C = sys.argv[1]
os.environ['RESERVE_N'] = '0'
N = int(os.environ.get('RESERVE4_N', '20'))
YEAR_FLOOR = int(os.environ.get('YEAR_FLOOR', '2018'))
import re
VER = re.compile(r'(?i)(verified|checked|confirmed|computer|computation(al|s)?|numerical(ly)? (evidence|experiments)|exhaustive|up to n ?=|for all n ?(≤|\\le|<=)|for n ?(≤|\\le|<=) ?\d|through n ?=|for small)')
STRONG = re.compile(r'(?i)(verified|checked|confirmed)[^.]{0,80}(up to|for all|through|for n|for every|when)')
sys.argv = ['reserve2.py', C]
g = runpy.run_path(C + '/root-intake-r60/reserve2.py', run_name='__main__')
el = {r['mathdb_id']: r for r in g['el']}
B = g['B']
DISC = g['DISC']
meta = {}
for ch in sorted(glob.glob(str(B / 'lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-*.jsonl'))):
    for line in open(ch, encoding='utf8'):
        try:
            d = json.loads(line)
        except Exception:
            continue
        if d.get('mathdb_id') in el:
            meta[d['mathdb_id']] = d


def year(d):
    try:
        return int(d.get('first_stated_year'))
    except Exception:
        return None


def disc(d):
    s = (' '.join(d.get('tags') or []) + ' ' + (d.get('title') or '')).lower()
    return any(k in s for k in DISC)


pool = []
for i, d in meta.items():
    y = year(d)
    if y is None or y < YEAR_FLOOR:
        continue
    if (d.get('solution_count') or 0) != 0 or not disc(d):
        continue
    if not VER.search(d.get('statement') or ''):
        continue
    pool.append(el[i])


def key(r):
    t = set(r['screening_tags'])
    d = meta[r['mathdb_id']]
    st = d.get('statement') or ''
    return (-bool(STRONG.search(st)), ('hard_structural' in t), -('few_quantified_parameters' in t),
            -(('elementary_inequality_cue' in t) or ('identity_or_closed_form_cue' in t)),
            -r['review_priority_score'], -(year(d) or 0), r['mathdb_id'])


pool.sort(key=key)
pick = pool[:N]
prev = g['prev']
out = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'kind': prev['kind'],
       'ids': [r['mathdb_id'] for r in pick],
       'rows': [dict(r, mathdb_tags=meta[r['mathdb_id']].get('tags') or [],
                     first_stated_year=year(meta[r['mathdb_id']]),
                     source_url=meta[r['mathdb_id']].get('source_url')) for r in pick],
       'input_hashes': {str(p): g['h'](p) for p in [g['COV'], g['Q'], g['TAGS']]},
       'excluded_ids_count': len(g['bad']), 'eligible_metadata_rows_after_filters': len(el),
       'recent_discrete_pool': len(pool),
       'selection': 'reserve5 (statement cites computational verification, strong verified-up-to phrase first) on top of reserve4: same eligibility and exclusions as earlier expanded-corpus reservations; restricted to first_stated_year >= %d, solution_count 0 and a discrete-mathematics keyword in MathDB tags or title; ranked by absence of hard_structural, few-parameter cue, inequality/identity cue, review score, newer year, then ID.' % YEAR_FLOOR,
       'limitation': prev['limitation'],
       'output_requirement': prev['output_requirement'].replace('Exactly40', 'Exactly %d' % len(pick))}
globals()['RESULT'] = out
