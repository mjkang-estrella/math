import pathlib,json,hashlib,subprocess,re
O=pathlib.Path(__file__).resolve().parent;der=json.loads((O/'derivative-bindings.json').read_text());out=[]
for name,page,pat in [('cayley',22,'3n'),('permutations',10,'Conjecture 1'),('permutations',11,'Question'),('permutations',33,'Conjecture 1'),('permutations',31,'Question.')]:
 p=O/f'{name}-p{page}.txt'
 if not p.exists():
  subprocess.run(['pdftotext','-f',str(page),'-l',str(page),'-layout',str(O/(name+'.pdf')),str(p)],check=True);b=p.read_bytes();der.append({'path':p.name,'parent':name+'.pdf','pdf_page':page,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)});(O/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
 s=p.read_text();m=re.search(pat,s,re.I)
 if m:
  excerpt=s[max(0,m.start()-150):m.end()+1100];out.append({'derivative':p.name,'anchor':pat,'excerpt':excerpt});print(p.name,excerpt)
 else:print(p.name,'anchor not found')
(O/'selected-excerpts.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
