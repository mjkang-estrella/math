#!/usr/bin/env python3
"""Read-only: print selected fields of a JSON file (treated as untrusted data).
Usage: jsonpick.py FILE MODE
 MODE work   : OpenAlex work summary (id, title, doi, year, cited_by_count, cited_by_api_url, authorships ids, locations)
 MODE list   : OpenAlex list results (id, year, title, doi, first author)
 MODE gh     : GitHub search results (total_count, items full_name/html_url/title)
 MODE keys   : top-level keys
 MODE raw    : print whole (first 6000 chars)"""
import json, sys
d = json.load(open(sys.argv[1], encoding='utf-8'))
m = sys.argv[2]
if m == 'work':
    print('id', d.get('id')); print('title', d.get('title')); print('doi', d.get('doi'))
    print('year', d.get('publication_year'), 'cited_by_count', d.get('cited_by_count'))
    print('cited_by_api_url', d.get('cited_by_api_url'))
    for a in d.get('authorships', []):
        print('author', a.get('author', {}).get('display_name'), a.get('author', {}).get('id'))
    for l in d.get('locations', []):
        print('location', (l.get('source') or {}).get('display_name'), l.get('landing_page_url'), l.get('pdf_url'))
    print('related/ids', d.get('ids'))
elif m == 'list':
    print('count', d.get('meta', {}).get('count'))
    for w in d.get('results', []):
        au = ', '.join(a.get('author', {}).get('display_name', '') for a in w.get('authorships', [])[:4])
        print(w.get('publication_year'), w.get('id'), '|', w.get('title'), '|', w.get('doi'), '|', au)
elif m == 'gh':
    if isinstance(d, dict):
        print('total_count', d.get('total_count'), 'incomplete', d.get('incomplete_results'), 'message', d.get('message'))
        for it in d.get('items', []):
            print(it.get('full_name') or it.get('title'), it.get('html_url'), (it.get('description') or '')[:120])
        if 'sha' in d:
            print('sha', d['sha'], 'date', d.get('commit', {}).get('committer', {}).get('date'), 'msg', d.get('commit', {}).get('message', '')[:200])
    else:
        for it in d:
            print(it.get('type'), it.get('name'), it.get('path'))
elif m == 'abstracts':
    for w in d.get('results', []):
        inv = w.get('abstract_inverted_index') or {}
        pos = sorted((p, t) for t, ps in inv.items() for p in ps)
        print('##', w.get('title'))
        print(' '.join(t for _, t in pos)[:1500])
elif m == 'keys':
    print(list(d.keys()) if isinstance(d, dict) else type(d))
else:
    print(json.dumps(d, indent=1)[:6000])
