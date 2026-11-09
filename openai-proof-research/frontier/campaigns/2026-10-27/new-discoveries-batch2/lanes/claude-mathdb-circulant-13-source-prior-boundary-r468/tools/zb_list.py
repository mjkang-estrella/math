"""List zbMATH Open API search results: id, year, title, authors, source, review text.
usage: zb_list.py BODY OUT.json"""
import json, sys

d = json.load(open(sys.argv[1]))
out = {'status': d.get('status'), 'entries': []}
for r in d.get('result', []):
    def g(*ks, base=r):
        x = base
        for k in ks:
            if isinstance(x, list):
                x = x[0] if x else None
            x = (x or {}).get(k) if isinstance(x, dict) else None
        return x
    titles = r.get('title') or {}
    srcs = r.get('source') or {}
    out['entries'].append({
        'zbl_id': r.get('identifier'), 'id': r.get('id'), 'year': r.get('year'),
        'title': titles.get('title') if isinstance(titles, dict) else titles,
        'authors': [a.get('name') for a in (r.get('contributors') or {}).get('authors', [])],
        'source': (srcs.get('series') or [{}])[0].get('title') if isinstance(srcs, dict) and srcs.get('series') else None,
        'doi': [l.get('identifier') for l in r.get('links', []) if l.get('type') == 'doi'],
        'review': ' '.join(((r.get('editorial_contributions') or [{}])[0].get('text') or '').split()),
    })
json.dump(out, open(sys.argv[2], 'w'), indent=1, ensure_ascii=False)
print(out['status'], len(out['entries']))
for x in out['entries']:
    print(x['year'], x['zbl_id'], '|', (x['title'] or '')[:95], '|', '; '.join(x['authors'])[:60])
