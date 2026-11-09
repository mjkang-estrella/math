import pathlib, json, sys, re
# usage: history.py LANE_DIR ROOT_TO_SCAN ; scoped to *.md, *results*.json, *ledger*.json, *review*.json
D = pathlib.Path(sys.argv[1]).resolve()
R = pathlib.Path(sys.argv[2]).resolve()
ex = json.loads((D / 'extracted.json').read_text())
pats = [str(i) for i in ex] + [arxiv for arxiv in
        {re.sub(r'.*/abs/', '', o['source_url']) for o in ex.values()}]
hits = []
for p in R.rglob('*'):
    if not p.is_file():
        continue
    s = str(p)
    if '/expanded-corpus-r223/' in s or '/corpus/' in s or '/raw/' in s:
        continue
    n = p.name
    if not (n.endswith('.md') or (n.endswith('.json') and any(k in n for k in ('results', 'ledger', 'review', 'status', 'exclu')))):
        continue
    try:
        if p.stat().st_size > 30_000_000:
            continue
        t = p.read_text(errors='replace')
    except Exception:
        continue
    for pat in pats:
        if pat in t:
            for ln, line in enumerate(t.splitlines(), 1):
                if pat in line:
                    hits.append({'file': s, 'line': ln, 'pattern': pat, 'text': line[:300]})
out = D / 'outputs' / ('history-' + R.name + '.json')
out.write_text(json.dumps(hits, indent=1) + '\n')
from collections import Counter
print(len(hits), Counter(h['pattern'] for h in hits))
for h in hits[:80]:
    print(h['pattern'], h['file'].replace(str(R), ''), h['line'], h['text'][:160])
