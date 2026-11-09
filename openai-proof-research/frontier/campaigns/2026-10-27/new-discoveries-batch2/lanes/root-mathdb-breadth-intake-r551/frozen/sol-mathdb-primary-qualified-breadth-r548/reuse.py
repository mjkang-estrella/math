import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;S=P.parent/'sol-mathdb-primary-qualified-breadth-r406'
def e(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
paths=[S/'manifest.json',S/'provenance.json',S/'primary/hayman.pdf',S/'primary/hayman.txt']
refs=[e(p) for p in paths]
(P/'source-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
m=json.loads(paths[0].read_text());print('manifest keys',m.keys())
for p in paths[1:]:
 v=next(x for x in m['files'] if x['path']==str(p.relative_to(S)))
 a=e(p);assert a['sha256']==v['sha256'] and a['size']==v.get('size',v.get('bytes'))
print(paths[1].read_text())
