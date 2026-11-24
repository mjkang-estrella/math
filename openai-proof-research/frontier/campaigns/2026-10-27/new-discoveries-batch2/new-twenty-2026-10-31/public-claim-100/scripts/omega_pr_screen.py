#!/usr/bin/env python3
"""Screen every counted row against GitHub pull requests of the-omega-institute/trureturing by the source's arXiv id.
Writes public-claim-100/omega-pr-screen.json. One search per row, 3 s apart (search limit 30/min)."""
import json, re, subprocess, time, os, sys, glob
P = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); C = os.path.dirname(P)
ev = json.load(open(os.path.join(P, 'claim-evidence.json')))
rows = ev['rows'] if isinstance(ev, dict) and 'rows' in ev else ev
src = {}
for f in sorted(glob.glob(os.path.join(C, '../lanes/pi-mathdb-full-corpus-inventory-r301/corpus/*.jsonl'))):
    for line in open(f, encoding='utf-8'):
        m = re.search(r'"mathdb_id": (\d+),', line)
        if m: src[int(m.group(1))] = line
out_p = os.path.join(P, 'omega-pr-screen.json')
out = json.load(open(out_p)) if os.path.exists(out_p) else {}
want = [r for r in rows if r.get('status') in ('CLEARED_ADVERSARIAL', 'TIER2_SEARCH_EASY', 'SOURCE_SCOPE', 'BLOCKED_ON_SOURCE')]
for r in want:
    i = int(r['mathdb_id'])
    if str(i) in out and 'error' not in out[str(i)]: continue
    line = src.get(i)
    if not line: out[str(i)] = {'error': 'no corpus row'}; continue
    rec = json.loads(line); url = rec.get('source_url') or ''
    m = re.search(r'arxiv\.org/abs/([^\s?#]+)', url)
    q = m.group(1).split('v')[0] if m else None
    if q and '/' in q: q = q.split('/')[-1]
    if not q:
        out[str(i)] = {'error': 'no arXiv id', 'source_url': url}; json.dump(out, open(out_p, 'w'), indent=1); continue
    c = subprocess.run(['gh', 'search', 'prs', '--repo', 'the-omega-institute/trureturing', q, '--limit', '10', '--json', 'number,title,createdAt,state'], capture_output=True, text=True)
    if c.returncode != 0:
        out[str(i)] = {'error': c.stderr.strip()[:200], 'query': q}
        json.dump(out, open(out_p, 'w'), indent=1); time.sleep(20); continue
    out[str(i)] = {'query': q, 'title': rec.get('title'), 'hits': json.loads(c.stdout or '[]')}
    json.dump(out, open(out_p, 'w'), indent=1, ensure_ascii=False)
    time.sleep(3.2)
n = sum(1 for v in out.values() if v.get('hits'))
print('rows screened', len(out), 'with hits', n, 'errors', sum(1 for v in out.values() if 'error' in v))
