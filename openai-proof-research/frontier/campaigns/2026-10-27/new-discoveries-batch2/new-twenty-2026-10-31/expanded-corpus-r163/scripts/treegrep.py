import json,sys,re
pats=[p.lower() for p in sys.argv[2].split(',')]
for f in sys.argv[1].split(','):
    d=json.load(open(f)); paths=[t['path'] for t in d['tree']]
    hits=[p for p in paths if any(k in p.lower() for k in pats)]
    print(f,'truncated',d.get('truncated'),'paths',len(paths),'hits',len(hits)); [print('  ',h) for h in hits[:40]]
