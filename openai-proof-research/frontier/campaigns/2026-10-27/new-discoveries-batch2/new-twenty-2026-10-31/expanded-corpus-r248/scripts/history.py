"""Scoped history search: prior campaign prose/structured conclusions (*.md, *review*.json, *results*.json,
*ledger*.json, *ruling*.json, *adjudication*.json, *disposition*.json) under new-discoveries-batch2,
for the 20 reserved IDs, arXiv source IDs and titles. Prunes .lake/build/sources/texts/raw/corpus/tmp directories.
Excludes this lane. Writes history-matches.txt (refuses overwrite)."""
import pathlib, json, re, fnmatch, os, sys
D = pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248')
root = D.parent.parent
out = D / 'history-matches.txt'
if out.exists():
    raise SystemExit('exists')
ex = json.loads((D / 'extracted.json').read_text())
keys = []
for i, o in ex.items():
    keys.append(i)
    keys.append(o['source_url'].rsplit('/', 1)[1])
    keys.append(o['title'].lower())
globs = ['*.md', '*review*.json', '*results*.json', '*ledger*.json', '*ruling*.json', '*adjudication*.json', '*disposition*.json']
prune = {'.lake', 'build', 'sources', 'texts', 'raw', 'corpus', 'tmp', 'http', 'logs', 'lake-packages', '.git', 'packages', 'build-copy', '.replays'}
lines = []
nfiles = 0
for dp, dns, fns in os.walk(root):
    dns[:] = [d for d in dns if d not in prune and os.path.join(dp, d) != str(D)]
    for fn in fns:
        if not any(fnmatch.fnmatch(fn, g) for g in globs):
            continue
        p = os.path.join(dp, fn)
        try:
            if os.path.getsize(p) > 20_000_000:
                continue
            t = open(p, errors='replace').read()
        except OSError:
            continue
        nfiles += 1
        low = t.lower()
        for k in keys:
            pos = low.find(k)
            n = 0
            while pos != -1 and n < 5:
                a = max(0, pos - 160)
                lines.append(f'{p}::{k}::' + t[a:pos + len(k) + 200].replace('\n', ' '))
                n += 1
                pos = low.find(k, pos + 1)
out.write_text(f'files scanned {nfiles}\n' + '\n'.join(lines) + '\n')
from collections import Counter
c = Counter(l.split('::')[1] for l in lines)
print('files', nfiles, 'hits', len(lines))
for k, v in c.most_common():
    print(k, v)
