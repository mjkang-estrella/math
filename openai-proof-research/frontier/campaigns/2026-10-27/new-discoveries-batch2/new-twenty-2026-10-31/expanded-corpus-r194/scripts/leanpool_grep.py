import json,sys,re
t=json.load(open(sys.argv[1])); paths=[x['path'] for x in t['tree']]
print('truncated',t.get('truncated'),'entries',len(paths))
print([p for p in paths if p.endswith(('.yml','.yaml'))][:20])
kw=sys.argv[2:]
for p in paths:
    if any(k.lower() in p.lower() for k in kw): print('HIT',p)
