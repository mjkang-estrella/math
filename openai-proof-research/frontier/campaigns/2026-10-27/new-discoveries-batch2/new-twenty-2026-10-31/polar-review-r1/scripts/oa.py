#!/usr/bin/env python3
"""Summarise downloaded OpenAlex / GitHub JSON (read-only).  usage: oa.py MODE FILE [FILTER_REGEX]"""
import json, re, sys
mode, fn = sys.argv[1], sys.argv[2]
flt = re.compile(sys.argv[3], re.I) if len(sys.argv) > 3 else None
d = json.load(open(fn))
def wline(w):
    au = ', '.join(a['author']['display_name'] for a in w.get('authorships', [])[:4])
    src = ((w.get('primary_location') or {}).get('source') or {}).get('display_name')
    return f"{w.get('publication_date')} | {w.get('id')} | {w.get('doi')} | cited_by={w.get('cited_by_count')} | {src} | {au} | {w.get('display_name')}"
if mode == 'work':
    print(wline(d)); print('cited_by_api_url', d.get('cited_by_api_url'))
    print('locations', [ (l.get('landing_page_url')) for l in d.get('locations', [])])
    print('counts_by_year', d.get('counts_by_year'))
elif mode == 'list':
    print('meta', d.get('meta'))
    for w in d.get('results', []):
        s = wline(w)
        if flt is None or flt.search(s): print(s)
elif mode == 'authors':
    for a in d.get('results', []):
        print(a.get('id'), '|', a.get('display_name'), '| works', a.get('works_count'), '| cited', a.get('cited_by_count'),
              '|', (a.get('last_known_institutions') or [{}])[0].get('display_name') if a.get('last_known_institutions') else None)
elif mode == 'ghsearch':
    print('total_count', d.get('total_count'), 'incomplete', d.get('incomplete_results'))
    for it in d.get('items', []):
        print(it.get('full_name'), '|', it.get('updated_at'), '|', (it.get('description') or '')[:150])
elif mode == 'ghcommit':
    print(d.get('sha'), d.get('commit', {}).get('committer', {}).get('date'), d.get('commit', {}).get('message', '')[:200])
elif mode == 'ghcontents':
    for it in d if isinstance(d, list) else [d]:
        s = f"{it.get('type')} {it.get('path')} {it.get('size')}"
        if flt is None or flt.search(s): print(s)
elif mode == 'ghtree':
    hits = [t['path'] for t in d.get('tree', []) if flt is None or flt.search(t['path'])]
    print('truncated', d.get('truncated'), 'entries', len(d.get('tree', [])), 'hits', len(hits))
    for h in hits[:200]: print(h)
