import pathlib,json,hashlib,subprocess
O=pathlib.Path(__file__).resolve().parent;d=json.loads((O/'derivative-bindings.json').read_text());out=[]
for name,needle in [('13853','Theorem. Every positive integer other than'),('13490','continuous map ∆100'),('14219','Theorem 3 (Giannopoulos-Koldobsky)')]:
 p=O/('ems'+name+'.txt');entry=next(x for x in d if x['path']==str(p));assert hashlib.sha256(p.read_bytes()).hexdigest()==entry['sha256']
 pages=p.read_text().split('\f');page=next(i+1 for i,s in enumerate(pages) if needle in s);prefix=O/('selected-'+name)
 subprocess.run(['pdftoppm','-f',str(page),'-l',str(page),'-scale-to','1400','-singlefile','-png',str(p.with_suffix('.pdf')),str(prefix)],check=True)
 im=prefix.with_suffix('.png');b=im.read_bytes();out.append(dict(path=str(im),size=len(b),sha256=hashlib.sha256(b).hexdigest(),pdf_page=page,parent=str(p.with_suffix('.pdf'))))
(O/'image-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
