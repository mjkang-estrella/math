exec(open(__file__.replace('freeze_graphs.py','freeze.py')).read().split("for name in ['AUDIT.md'")[0])
for name in ['G-edges.json','H-edges.json','graph-certificates.json']:
    freeze(B/'sol-fullerene-heat-trace-breadth-depth-r286'/name,'frozen')
old=json.loads((L/'source-bindings.json').read_text())
(L/'source-bindings.json').write_text(json.dumps(old+entries,indent=2)+'\n')
print('frozen original graph certificates')
