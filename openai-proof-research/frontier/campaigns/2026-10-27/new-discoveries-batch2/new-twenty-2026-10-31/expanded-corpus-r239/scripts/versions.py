import pathlib,json,re,importlib.util,subprocess,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; spec=importlib.util.spec_from_file_location('lh',D/'scripts/http.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
out={}
for p in sorted((D/'sources').glob('*.abs.html')):
 a=p.name.split('.abs')[0]; s=p.read_text(); v=sorted(set(re.findall(r'\['+r'v(\d+)'+r'\]',s)),key=int);out[a]={'versions':v}
 for n in v:
  h.get(a+'v'+n+'.pdf','https://arxiv.org/pdf/'+a+'v'+n)
(D/'versions.json').write_text(json.dumps(out,indent=2)+'\n')
for p in (D/'sources').glob('*.pdf'):
 if not p.with_suffix('.txt').exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
