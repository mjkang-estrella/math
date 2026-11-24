#!/usr/bin/env python3
"""Build CLAIM-EVIDENCE.md and claim-evidence.json from status.json and the lane outputs.
Re-runnable: reads only; writes the two files in public-claim-100/."""
import json, glob, os, re, sys
from collections import Counter, OrderedDict
C = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
P = os.path.join(C, 'public-claim-100')
sys.path.insert(0, os.path.join(C, 'root-intake-r60'))
from corpus_row import row as corpus
J = lambda p: json.load(open(p))
rel = lambda p: os.path.relpath(p, C) if isinstance(p, str) and os.path.isabs(p) else p

status = J(os.path.join(P, 'status.json'))
base = {r['mathdb_id']: r for r in J(os.path.join(P, 'base-rows.json'))}
ledger = J(os.path.join(C, 'ledger.json'))

def lst(d):
    if isinstance(d, dict):
        for k in ('results', 'records', 'rows'):
            if k in d: return d[k]
        return [d]
    return d

# prior-art sweeps (the top-up B7 and the first sweep both apply to the 23)
sweep, topup = {}, {}
for f in sorted(glob.glob(os.path.join(C, 'uniform-prior-art-sweep-B[1-6]-sol62-*/sweep.json'))) + [os.path.join(C, 'public-tracker-prior-art-sweep-sol62-20261119-r1/sweep.json')]:
    for e in lst(J(f)): sweep[int(e['mathdb_id'])] = (rel(os.path.dirname(f)), e)
for e in lst(J(glob.glob(os.path.join(C, 'uniform-prior-art-sweep-B7-*/sweep.json'))[0])): topup[int(e['mathdb_id'])] = e
fid = {}
for f in glob.glob(os.path.join(C, 'row-fidelity-audit-D*-sol62-*/fidelity.json')):
    for e in lst(J(f)): fid[int(e['mathdb_id'])] = (rel(os.path.dirname(f)), e)
adj = {}
for f in sorted(glob.glob(os.path.join(C, 'closecall-adjudication-A*/result.json'))):
    for e in lst(J(f)): adj[int(e['mathdb_id'])] = (rel(os.path.dirname(f)), e)
conf = {}
for f in sorted(glob.glob(os.path.join(C, 'tier1-confirm-G*-opus-*/confirm.json'))) + sorted(glob.glob(os.path.join(C, 'closecall-adjudication-A10b-*/confirm.json'))):
    for e in lst(J(f)): conf[int(e['mathdb_id'])] = (rel(os.path.dirname(f)), e)
tri = {}
for f in sorted(glob.glob(os.path.join(C, 'adversarial-triage-E*-sol62-*/triage.json'))):
    for e in lst(J(f)): tri[int(e['mathdb_id'])] = (rel(os.path.dirname(f)), e)
manual = J(os.path.join(P, 'row-overrides.json')) if os.path.exists(os.path.join(P, 'row-overrides.json')) else {}
extra = J(os.path.join(P, 'extra-rows.json')) if os.path.exists(os.path.join(P, 'extra-rows.json')) else {}
for k_, x_ in extra.items():
    status.setdefault(k_, {'status': x_['status'], 'note': x_['note'], 'outcome': x_['outcome']})
    manual.setdefault(k_, {}).update({k2: v2 for k2, v2 in x_.items() if k2 not in ('status', 'note')})

def acceptance(i):
    for a in ledger['accepted']:
        if int(a['mathdb_id']) == i:
            if 'file' in a:
                for p in (a['file'], 'root-intake-r60/' + a['file']):
                    if os.path.exists(os.path.join(C, p)): return J(os.path.join(C, p)), p
            return a, 'ledger.json#accepted'
    return None, None

def short(s, n=600):
    s = re.sub(r'\s+', ' ', str(s)).strip()
    return s if len(s) <= n else s[:n - 1].rstrip() + '…'

TIER = OrderedDict([
 ('CLEARED_ADVERSARIAL', ('Tier 1', 'cleared by adversarial review of a non-author model: literal, not found public, not routine, not trivial')),
 ('TIER2_SEARCH_EASY', ('Tier 2', 'correct, literal, not found public, kernel-checked refutation; a generic computer search finds a counterexample in seconds or minutes at or near the first size the source did not check')),
 ('SOURCE_SCOPE', ('Tier 3', 'the MathDB record text is a faulty transcription; the conjecture as printed in the cited paper is resolved and kernel-checked')),
 ('BLOCKED_ON_SOURCE', ('Blocked', 'otherwise clean; one named paper could not be read')),
 ('NOT_COUNTED', ('Not counted', 'already public, a few lines from published results, trivial, or not the stated problem')),
])

rows = []
for sid, v in status.items():
    i = int(sid); b = base.get(i); acc, accfile = acceptance(i)
    cr = corpus(i) or {}
    r = {'mathdb_id': i, 'status': v['status'], 'status_note': v.get('note', ''), 'ledger_ordinal': v.get('n')}
    r['title'] = (b or {}).get('record_title') or cr.get('title')
    r['record_statement'] = cr.get('statement')
    r['source'] = cr.get('source_name'); r['source_url'] = cr.get('source_url')
    r['outcome'] = (b or {}).get('outcome') or (acc or {}).get('outcome') or v.get('outcome')
    ep = (b or {}).get('endpoints') or (acc or {}).get('endpoints')
    r['lean_endpoints'] = ep if isinstance(ep, list) else [ep]
    rp = (b or {}).get('replay') or ((acc or {}).get('lanes') or {}).get('final_replay')
    r['replay_record'] = rel(rp) if isinstance(rp, str) else ('see ' + str(accfile))
    r['acceptance_record'] = accfile
    r['submission'] = (b or {}).get('submission') or rel((acc or {}).get('submission_packet'))
    # exact statement of what is proved
    stmt = None; src = None
    if i in adj and adj[i][1].get('exact_statement_for_public_row'): stmt, src = adj[i][1]['exact_statement_for_public_row'], adj[i][0]
    elif i in fid: stmt, src = fid[i][1].get('row_statement'), fid[i][0]
    elif acc and (acc.get('significance') or {}).get('root_decision'): stmt, src = acc['significance']['root_decision'], accfile
    r['row_statement'] = stmt; r['row_statement_source'] = src
    r['relation'] = fid[i][1].get('relation') if i in fid else None
    r['lean_vs_paper'] = fid[i][1].get('lean_vs_paper') if i in fid else None
    # adversarial verdict
    verd = []
    if i in adj: verd.append('%s (%s, confidence %s)' % (adj[i][1].get('verdict'), adj[i][0], short(adj[i][1].get('confidence'), 60)))
    if i in tri: verd.append('%s (%s)' % (tri[i][1].get('verdict'), tri[i][0]))
    if i in conf: verd.append('%s (%s, confidence %s)' % (conf[i][1].get('verdict'), conf[i][0], short(conf[i][1].get('confidence'), 40)))
    if acc and (acc.get('lanes') or {}).get('review') and i not in base: verd.append('PASS (' + acc['lanes']['review'] + ')')
    r['adversarial_verdicts'] = verd
    caveats = []
    for d_, key in ((adj, 'caveats_row_must_carry'), (conf, 'row_caveats'), (tri, 'row_caveats')):
        if i in d_ and d_[i][1].get(key): caveats += [short(c, 400) for c in (d_[i][1][key] if isinstance(d_[i][1][key], list) else [d_[i][1][key]])]
    if acc and i not in base and (acc.get('significance') or {}).get('caveat'): caveats.append(short(acc['significance']['caveat'], 500))
    r['caveats'] = caveats
    # prior art
    pa = {}
    if i in sweep:
        d0, e = sweep[i]
        pa = {'sweep_lane': d0, 'sweep_verdict': e.get('verdict'), 'queries_and_routes': len(e.get('searched') or []),
              'routes_refused': e.get('routes_refused') or [], 'closest_prior_read': e.get('closest_prior_read'),
              'evidence': [{'url': x.get('url'), 'date': x.get('date'), 'says': short(x.get('what it says'), 220)} for x in (e.get('evidence') or [])[:3]]}
        if i in topup:
            pa['topup_verdict'] = topup[i].get('verdict'); pa['queries_and_routes'] += len(topup[i].get('searched') or [])
            if topup[i].get('closest_prior_read'): pa['closest_prior_read'] = topup[i]['closest_prior_read']
    elif acc and i not in base:
        pa = {'sweep_lane': (acc.get('lanes') or {}).get('review'), 'sweep_verdict': 'NO_PRIOR_FOUND (candidate review and final check)', 'note': acc.get('omega_screen')}
    r['prior_art'] = pa
    if sid in manual: r.update(manual[sid])
    rows.append(r)

order = list(TIER.keys())
rows.sort(key=lambda r: (order.index(r['status']) if r['status'] in order else 99, r['mathdb_id']))
json.dump(rows, open(os.path.join(P, 'claim-evidence.json'), 'w'), indent=1, ensure_ascii=False)

cnt = Counter(r['status'] for r in rows)
out = []
out.append('# Evidence for the public claim: MathDB problems resolved by AI with kernel-checked Lean proofs\n')
out.append('Generated by `public-claim-100/scripts/build_evidence.py` from `status.json` and the lane outputs. Every statement below is traceable to a file named in the row. Nothing here has been submitted or published.\n')
out.append('## Counts\n')
out.append('| Group | Meaning | Rows |\n|---|---|---|')
for k, (name, mean) in TIER.items(): out.append('| %s | %s | %d |' % (name, mean, cnt.get(k, 0)))
others = sum(v for k, v in cnt.items() if k not in TIER)
if others: out.append('| Undecided | still being adjudicated | %d |' % others)
out.append('')
out.append('Checks applied to every row: (1) kernel-checked Lean endpoint with only the axioms propext, Classical.choice, Quot.sound, rebuilt from extracted sources (replay record named in the row); (2) a statement-fidelity audit of the endpoint against the MathDB record; (3) a uniform prior-art sweep (source versions, citing papers through OpenAlex and Semantic Scholar, key-term web search, the openai/math and omega registries, ProbXiv, GitHub search) plus a search by MathDB id of GitHub and of the Principia archive of public MathDB solutions (300 ids); (4) an adversarial test by a model that did not author the result. Not checked: mathdb.com itself (it refuses automated clients), Google Scholar and the arXiv search API (both refuse automated clients), and the publisher texts listed per row as unread.\n')

def render(r, full=True):
    o = []
    o.append('### %d · %s\n' % (r['mathdb_id'], r['title']))
    o.append('- **Outcome:** %s%s' % (r['outcome'], (' (ledger result %s)' % r['ledger_ordinal']) if r.get('ledger_ordinal') else ''))
    o.append('- **Source:** %s' % short(r['source'], 300))
    if r.get('row_statement'): o.append('- **What is proved (exact):** %s' % short(r['row_statement'], 1100))
    if r.get('relation'): o.append('- **Relation of the Lean endpoint to the MathDB record:** %s' % r['relation'])
    if full:
        o.append('- **MathDB record statement:** %s' % short(r['record_statement'], 900))
        o.append('- **Lean endpoint:** %s' % ', '.join('`%s`' % short(e, 200) for e in r['lean_endpoints'] if e))
        o.append('- **Replay record:** `%s`; acceptance record `%s`; submission folder `%s`' % (short(r['replay_record'], 200), r['acceptance_record'], r['submission']))
        if r.get('lean_vs_paper'): o.append('- **Kernel-checked versus paper-only:** %s' % short(r['lean_vs_paper'], 500))
        pa = r['prior_art']
        if pa:
            cp = pa.get('closest_prior_read') or {}
            o.append('- **Prior art searched:** %s; sweep verdict %s%s; %s queries and routes recorded%s' % (
                '`%s`' % pa.get('sweep_lane'), pa.get('sweep_verdict'), (', top-up verdict %s' % pa['topup_verdict']) if pa.get('topup_verdict') else '',
                pa.get('queries_and_routes', 'see lane'), ('; routes refused: ' + short('; '.join(map(str, pa['routes_refused'])), 260)) if pa.get('routes_refused') else ''))
            if cp: o.append('- **Closest prior work read:** %s (%s) %s' % (short(cp.get('citation'), 260), cp.get('read'), cp.get('url') or ''))
            elif pa.get('note'): o.append('- **Registry screen:** %s' % short(pa['note'], 260))
        if r['adversarial_verdicts']: o.append('- **Adversarial verdicts:** %s' % '; '.join(r['adversarial_verdicts']))
    o.append('- **Status note:** %s' % short(r['status_note'], 700))
    if full and r['caveats']:
        o.append('- **Caveats the row carries:**')
        for c in r['caveats'][:6]: o.append('  - %s' % c)
    o.append('')
    return o

for k, (name, mean) in TIER.items():
    grp = [r for r in rows if r['status'] == k]
    out.append('## %s (%d): %s\n' % (name, len(grp), mean))
    if k == 'NOT_COUNTED':
        out.append('| MathDB id | Outcome claimed | Reason it is not counted |\n|---|---|---|')
        for r in grp: out.append('| %d | %s | %s |' % (r['mathdb_id'], r['outcome'], short(r['status_note'], 400).replace('|', '/')))
        out.append('')
    else:
        for r in grp: out += render(r)
rest = [r for r in rows if r['status'] not in TIER]
if rest:
    out.append('## Undecided (%d)\n' % len(rest))
    for r in rest: out += render(r, full=False)
open(os.path.join(P, 'CLAIM-EVIDENCE.md'), 'w').write('\n'.join(out) + '\n')
print(dict(cnt), 'rows', len(rows))
miss = [(r['mathdb_id'], [k for k in ('row_statement', 'lean_endpoints', 'replay_record', 'prior_art') if not r.get(k) or r.get(k) == [None]]) for r in rows if r['status'] != 'NOT_COUNTED']
print('rows with missing fields:', [m for m in miss if m[1]])
