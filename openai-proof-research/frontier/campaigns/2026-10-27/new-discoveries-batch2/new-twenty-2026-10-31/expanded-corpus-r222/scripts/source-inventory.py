import pathlib,re,json,html
D=pathlib.Path(__file__).resolve().parents[1];out={}
for p in (D/'sources').glob('*.html'):
 if not re.match(r'\d{4}\.\d+v\d+\.html$',p.name):continue
 s=p.read_text();t=(D/'sources'/(p.stem+'.txt')).read_text();captions=[]
 for m in re.finditer(r'<figcaption\b[^>]*>(.*?)</figcaption>',s,re.S):
  captions.append(re.sub(r'\s+',' ',html.unescape(re.sub('<[^>]*>',' ',m[1]))).strip())
 out[p.stem]={'figure_captions':captions,'example_contexts':[t[max(0,m.start()-50):m.end()+850] for m in re.finditer(r'Example\s+\d+[.]\d+',t)],'conjecture_contexts':[t[max(0,m.start()-50):m.end()+1200] for m in re.finditer(r'Conjecture\s+\d+',t)],'limitation':'Text/caption inventory; no claim that every illustration was visually inspected or every proof independently checked.'}
(D/'source-inventory.json').write_text(json.dumps(out,indent=2))
