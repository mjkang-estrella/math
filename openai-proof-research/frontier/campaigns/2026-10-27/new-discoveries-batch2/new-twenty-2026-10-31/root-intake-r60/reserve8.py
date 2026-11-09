# reserve8 (root, 2026-11-04): reserve7 with classic colouring/edge-colouring and other famous names added to the FAMOUS penalty (r170 drew mostly famous colouring conjectures).
# reserve7 (root, 2026-11-03): reserve6 plus a FAMOUS-name penalty. Lanes r134-r136 spent most of their reservations on flagship
# structural conjectures (Hadwiger, Erdos-Hajnal, Menger, reconstruction, tangles, treewidth, minors) with no tractable finite route.
# reserve6 (root, 2026-11-03): finite, kernel-checkable discrete conjectures. Built on reserve5/reserve2 eligibility
# and exclusions (every prior */reservation.json assignment is excluded via reserve2). The reserve5 pool is nearly
# exhausted and mostly asymptotic; Lean cost has been the campaign bottleneck. reserve6 therefore drops the
# verification-phrase requirement, EXCLUDES statements with asymptotic/probabilistic/analytic cues, and ranks by
# finite-instance cues (explicit small parameters, every/there-exists over finite discrete objects, extremal numbers),
# then verification cue, absence of hard_structural, few-parameter cue, review score, newer year, then ID.
import os, sys, json, glob, datetime, runpy, re
C = sys.argv[1]
os.environ['RESERVE_N'] = '0'
N = int(os.environ.get('RESERVE7_N', '20'))
YEAR_FLOOR = int(os.environ.get('YEAR_FLOOR', '2012'))
ASYMP = re.compile(r'(?i)(asymptotic|sufficiently large|large enough|as \$?n ?(\\to|→|tends)|\\to ?\\infty|→ ?∞|\bo\(|\\Theta|\\Omega\(|\bΘ|\\log|\blog\b|\blim(it)?\b|almost (all|every|surely)|random|probabilit|expected|density|measure|integral|\\int|continuous|real-valued|manifold|lebesgue|banach|hilbert|infinitely many)')
FAMOUS = re.compile(r'(?i)(acyclic (edge )?colou?r|total colou?r|equitable (total )?colou?r|linear arboricity|1-2 conjecture|1-2-3 conjecture|burris|schelp|incidence colou?r|list colou?r|kadison|weaver|graham|hedetniemi|vizing|behzad|goldberg|seymour|berge|reed|hadwiger|erd(o|ő|ö)s|hajnal|menger|reconstruct|kelly|gy(a|á)rf(a|á)s|sumner|de bruijn|szemer(e|é)di|jackson|thomassen|steiner system|treewidth|tree-width|tangle|minor|coarse|lov(a|á)sz|tutte|hamiltonian cycle|four colou?r|graceful|caccetta|seymour|chv(a|á)tal|ringel|sidorenko|unique games|p ?(=|vs\.?) ?np|polynomial-time)')
FIN = [re.compile(p) for p in [
    r'(?i)\b[nkmrdtq] ?(=|\\geq|\\ge|≥|\\leq|\\le|≤) ?\d{1,2}\b',
    r'(?i)\b(every|each|any|all) (finite )?(simple )?(connected )?(graph|tree|tournament|matrix|matrices|permutation|hypergraph|digraph|poset|lattice|code|design|word|partition|polytope|set system|latin square|sequence)s?\b',
    r'(?i)there (exists?|is|are) (a|an|no|some)\b',
    r'(?i)\b(smallest|minimum|maximum|largest|least|exact(ly)?)\b',
    r'(?i)\b(verified|checked|confirmed|exhaustive|computer)\b',
    r'(?i)\b(\d{1,2})-(regular|uniform|connected|colou?r|chromatic|critical|vertex|edge)',
]]
sys.argv = ['reserve2.py', C]
g = runpy.run_path(C + '/root-intake-r60/reserve2.py', run_name='__main__')
el = {r['mathdb_id']: r for r in g['el']}
B = g['B']; DISC = g['DISC']
meta = {}
for ch in sorted(glob.glob(str(B / 'lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-*.jsonl'))):
    for line in open(ch, encoding='utf8'):
        try: d = json.loads(line)
        except Exception: continue
        if d.get('mathdb_id') in el: meta[d['mathdb_id']] = d
def year(d):
    try: return int(d.get('first_stated_year'))
    except Exception: return None
def disc(d):
    s = (' '.join(d.get('tags') or []) + ' ' + (d.get('title') or '')).lower()
    return any(k in s for k in DISC)
pool = []
for i, d in meta.items():
    y = year(d); st = d.get('statement') or ''
    if y is None or y < YEAR_FLOOR: continue
    if (d.get('solution_count') or 0) != 0 or not disc(d): continue
    if ASYMP.search(st) or ASYMP.search(d.get('title') or ''): continue
    pool.append(el[i])
def fin(r):
    st = meta[r['mathdb_id']].get('statement') or ''
    return sum(bool(p.search(st)) for p in FIN)
def key(r):
    t = set(r['screening_tags']); d = meta[r['mathdb_id']]
    fam = bool(FAMOUS.search((d.get('title') or '') + ' ' + (d.get('statement') or '')[:400]))
    return (fam, -fin(r), ('hard_structural' in t), -('few_quantified_parameters' in t),
            -r['review_priority_score'], -(year(d) or 0), r['mathdb_id'])
pool.sort(key=key)
pick = pool[:N]
prev = g['prev']
out = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'kind': prev['kind'],
       'ids': [r['mathdb_id'] for r in pick],
       'rows': [dict(r, mathdb_tags=meta[r['mathdb_id']].get('tags') or [], first_stated_year=year(meta[r['mathdb_id']]),
                     source_url=meta[r['mathdb_id']].get('source_url'), finite_cue_count=fin(r)) for r in pick],
       'input_hashes': {str(p): g['h'](p) for p in [g['COV'], g['Q'], g['TAGS']]},
       'excluded_ids_count': len(g['bad']), 'eligible_metadata_rows_after_filters': len(el),
       'finite_discrete_pool': len(pool),
       'selection': 'reserve8 (reserve7 with classic colouring names also penalised; reserve6 with flagship-name conjectures ranked last; finite, kernel-checkable discrete conjectures): same eligibility and exclusions as earlier expanded-corpus reservations; first_stated_year >= %d, solution_count 0, discrete keyword in MathDB tags or title; statements/titles with asymptotic, probabilistic or analytic cues excluded; ranked by finite-instance cue count, absence of hard_structural, few-parameter cue, review score, newer year, then ID.' % YEAR_FLOOR,
       'limitation': prev['limitation'],
       'output_requirement': prev['output_requirement'].replace('Exactly40', 'Exactly %d' % len(pick))}
globals()['RESULT'] = out
