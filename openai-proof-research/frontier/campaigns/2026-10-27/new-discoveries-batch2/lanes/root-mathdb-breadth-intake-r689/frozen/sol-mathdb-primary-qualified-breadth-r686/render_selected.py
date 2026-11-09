import pathlib,json,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parent;o=json.loads((L/'source-provenance.json').read_text())
for id,term,lo,hi in [(404190,'he made concrete',1114,1160),(404218,'In [7, 8] I conjectured',1579,1684),(404497,'Conjecture 7.',990,1040)]:
 t=(L/f'{id}.txt').read_text(); p=next(n for n,s in enumerate(t.split('\f'),1) if term in s)
 subprocess.run(['pdftoppm','-f',str(p),'-l',str(p),'-scale-to','1400','-singlefile','-png',str(L/f'{id}.pdf'),str(L/f'{id}-page')],check=True)
 for path in [L/f'{id}-page.png']:
  b=path.read_bytes();o.append({'id':id,'kind':'visual derivative bound before inspection','page':p,'path':path.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 path=L/f'{id}-selected.txt';path.write_text('\n'.join(t.splitlines()[lo-1:hi])+'\n');b=path.read_bytes();o.append({'id':id,'kind':'selected excerpt','source_lines':[lo,hi],'path':path.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'source-provenance.json').write_text(json.dumps(o,indent=2)+'\n')
