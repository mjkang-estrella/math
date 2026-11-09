import pathlib,json,hashlib,subprocess,re
O=pathlib.Path(__file__).resolve().parent;der=json.loads((O/'derivative-bindings.json').read_text())
for n in [31,33]:
 p=O/f'permutations-p{n}.txt';subprocess.run(['pdftotext','-f',str(n),'-l',str(n),'-layout',str(O/'permutations.pdf'),str(p)],check=True);b=p.read_bytes();der.append({'path':p.name,'parent':'permutations.pdf','pdf_page':n,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(O/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
for name,pat in [('permutations-p9.txt','Conjecture'),('permutations-p11.txt','rational'),('permutations-p31.txt','negative'),('permutations-p33.txt','Conjecture'),('cayley-p23.txt','diameter'),('designs-p21.txt','girth'),('designs-p62.txt','600')]:
 s=(O/name).read_text();matches=list(re.finditer(pat,s,re.I));print('\nEXCERPT',name)
 if not matches:print('ANCHOR NOT FOUND; no page content displayed');continue
 m=matches[0];a=max(0,s.rfind('\n',0,max(0,m.start()-300)));b=min(len(s),m.end()+1350);print(s[a:b])
