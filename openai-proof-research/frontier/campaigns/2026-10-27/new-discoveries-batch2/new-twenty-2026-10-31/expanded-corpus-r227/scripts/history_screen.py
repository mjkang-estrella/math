"""Scoped history screen: search *.md, *results*.json, *ledger*.json, *review*.json, *ruling*.json,
*disposition*.json under new-discoveries-batch2 (excluding raw corpus/tags dirs, reservation files and
this lane) for the 20 reserved IDs, their source arXiv IDs and short title keys.
Usage: history_screen.py LANE"""
import sys, json, pathlib, os, re
D = pathlib.Path(sys.argv[1]).resolve(); B = D.parent.parent
res = json.loads((D / 'reservation.json').read_text())
keys = {}
for r in res['rows']:
    i = str(r['mathdb_id']); keys[i] = [i, r['source_url'].rsplit('/', 1)[1]]
pat = re.compile('|'.join(re.escape(k) for v in keys.values() for k in v))
hits = {i: [] for i in keys}; scanned = 0
for root, dirs, files in os.walk(B):
    rp = pathlib.Path(root)
    if rp == D or D in rp.parents: dirs[:] = []; continue
    dirs[:] = [d for d in dirs if d not in ('corpus', 'tags', 'raw', 'frozen', '.lake', 'packages', 'sources', 'receipts', '.replays')]
    for f in files:
        if not (f.endswith('.md') or (f.endswith('.json') and re.search('result|ledger|review|ruling|disposition|integration|screen', f))):
            continue
        if f in ('reservation.json',) or 'reservation' in f: continue
        p = rp / f
        try:
            if p.stat().st_size > 30_000_000: continue
            t = p.read_text(errors='replace')
        except OSError:
            continue
        scanned += 1
        for m in pat.finditer(t):
            k = m.group(0)
            for i, v in keys.items():
                if k in v and len(hits[i]) < 12:
                    hits[i].append({'file': str(p.relative_to(B)), 'match': k, 'context': t[max(0, m.start() - 160):m.end() + 240]})
out = {'scanned_files': scanned, 'hits': hits}
(D / 'outputs' / 'history-screen.json').write_text(json.dumps(out, indent=1) + '\n')
print('scanned', scanned)
for i, h in hits.items():
    print(i, len(h), sorted({x['file'] for x in h})[:6])
