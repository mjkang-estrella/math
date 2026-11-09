import json, re, sys
pat = re.compile(r'conference|weighing|etzion|vardy|yaakobi|lee.?manhattan|manhattan|reed.?solomon|\bmds\b|mds[-_]|[-_]mds|self.?dual|hadamard|paley|324342|arasu|gulliver|grassl', re.I)
out = {}
for f in sys.argv[2:]:
    d = json.load(open(f)); hits = [x['path'] for x in d['tree'] if pat.search(x['path'])]
    out[f] = {"truncated": d.get('truncated'), "entries": len(d['tree']), "hits": hits}
    print(f, d.get('truncated'), len(d['tree']), len(hits)); [print('  ', h) for h in hits[:60]]
json.dump(out, open(sys.argv[1], 'w'), indent=1)
