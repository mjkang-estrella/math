"""Aggregate checker.py chunk outputs (381851) into outputs/checker/summary.json."""
import json, glob, pathlib
L = pathlib.Path(__file__).resolve().parents[1]
summ = {}
for f in sorted(glob.glob(str(L / 'outputs/checker/*.json'))):
    if f.endswith('summary.json'): continue
    d = json.load(open(f)); s = d['stats']; key = f"{s['p']}x{s['q']}"
    a = summ.setdefault(key, dict(chunks=set(), nchunks=s['nchunks'], matrices=0, classes=0, pairs_cond_i=0,
                                  pairs_cond_i_unreach=0, if_counterexamples=0, onlyif_fixedRC_failures=0, max_class=0))
    a['chunks'].add(s['chunk'])
    for k in ('matrices', 'classes', 'pairs_cond_i', 'pairs_cond_i_unreach', 'if_counterexamples', 'onlyif_fixedRC_failures'):
        a[k] += s[k]
    a['max_class'] = max(a['max_class'], s['max_class'])
for k, a in summ.items():
    a['complete'] = len(a['chunks']) == a['nchunks']; a['chunks'] = sorted(a['chunks'])
    a['expected_matrices'] = 2 ** (int(k.split('x')[0]) * int(k.split('x')[1]))
(L / 'outputs/checker/summary.json').write_text(json.dumps(summ, indent=1) + '\n')
print(json.dumps(summ))
