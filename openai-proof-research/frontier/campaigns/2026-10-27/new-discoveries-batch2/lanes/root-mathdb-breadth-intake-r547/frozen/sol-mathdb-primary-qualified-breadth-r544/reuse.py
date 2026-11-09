import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parent;L=D.parent
out=json.loads((D/'flat-bindings.json').read_text())
def bind(p,e=None):
 b=p.read_bytes();s={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 if e:assert s['sha256']==e['sha256'] and s['size']==e.get('size',e.get('bytes'))
 out.append(s)
for lane,stem in [('sol-mathdb-primary-qualified-breadth-r428','4080'),('sol-mathdb-primary-qualified-breadth-r436','12861'),('sol-mathdb-primary-qualified-breadth-r442','owr2017-20')]:
 P=L/lane;bind(P/'manifest.json');m=json.loads((P/'manifest.json').read_text())
 for e in m['files']:
  if e['path'] in ['sources/'+stem+'.pdf','sources/'+stem+'.txt','source-provenance.json','pdf-provenance.json','body-downloads.json','downloads.json','provenance.json']:
   bind(P/e['path'],e)
(D/'flat-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print('Bound reuse snapshots and provenance')
