"""Summarise history-matches.txt per reserved ID / title keyword (read-only).
Prints first lines, then for each ID the count of matching lines and distinct file paths
outside this lane, with a short snippet."""
import collections
import json
import pathlib
import sys

lane = pathlib.Path(sys.argv[1])
hm = (lane / 'history-matches.txt').read_text(errors='replace').splitlines()
print('lines', len(hm))
for l in hm[:3]:
    print('HEAD', l[:300])
ids = json.loads((lane / 'reservation.json').read_text())['ids']
keys = [str(i) for i in ids] + sys.argv[2:]
for k in keys:
    files = collections.OrderedDict()
    for l in hm:
        if k in l:
            f = l.split(':', 1)[0]
            if 'expanded-corpus-r245' in f:
                continue
            files.setdefault(f, []).append(l)
    print('==', k, 'files', len(files))
    for f, ls in list(files.items())[:12]:
        print('   ', f, len(ls), '|', ls[0][len(f):len(f) + 260].replace('\n', ' '))
