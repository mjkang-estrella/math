"""Print compact contexts of history-screen hits. Usage: show_hits.py LANE [ID ...]"""
import sys, json, pathlib, re
D = pathlib.Path(sys.argv[1]).resolve()
h = json.loads((D / 'outputs' / 'history-screen.json').read_text())['hits']
want = sys.argv[2:] or list(h)
skip = ('sepperm-proof-r1', 'schrijver-formal', 'chanlevine-formal', 'supervenience-')
for i in want:
    for x in h.get(i, []):
        if any(s in x['file'] for s in skip):
            continue
        c = re.sub(r'\s+', ' ', x['context'])
        print(i, '|', x['file'], '|', c[:400])
        print()
