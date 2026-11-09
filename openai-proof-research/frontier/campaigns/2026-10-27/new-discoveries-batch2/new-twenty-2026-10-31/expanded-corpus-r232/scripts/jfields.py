"""Print selected fields of fetched JSON files compactly.
Usage: jfields.py LANE FILE [FILE ...]  (files relative to LANE/sources)"""
import sys, json, pathlib
D = pathlib.Path(sys.argv[1]).resolve()
for f in sys.argv[2:]:
    o = json.loads((D / 'sources' / f).read_text())
    if isinstance(o, dict) and 'commit' in o:
        c = o['commit']
        print(f, 'sha', o.get('sha'), 'date', c['committer']['date'], 'msg', c['message'][:150].replace('\n', ' '))
        fl = o.get('files') or []
        print('   files', len(fl), [x['filename'] for x in fl[:12]])
    elif isinstance(o, dict):
        print(f, {k: o.get(k) for k in ['full_name', 'created_at', 'pushed_at', 'description', 'html_url', 'total_count']})
        for it in (o.get('items') or [])[:15]:
            print('   item', it.get('full_name'), it.get('created_at'), (it.get('description') or '')[:120])
    else:
        print(f, type(o), len(o))
