import pathlib,re,json,subprocess,hashlib,sys,importlib.util
D=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('fetch',D/'scripts/fetch.py');f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
versions={}
for p in sorted((D/'sources').glob('*.abs.html')):
 a=p.name[:-9]; h=p.read_text(); vs=sorted(set(re.findall(r'\b'+re.escape(a)+r'v(\d+)\b',h)),key=int)
 versions[a]=vs
 for v in vs:
  key=a+'v'+v+'.pdf'
  if not (D/'sources'/key).exists() and not (D/'sources'/(key+'.receipt.json')).exists():print(f.get((key,'https://arxiv.org/pdf/'+a+'v'+v)),flush=True)
(D/'outputs/versions.json').write_text(json.dumps(versions,indent=2)+'\n')
for p in (D/'sources').glob('*.pdf'):
 out=p.with_suffix('.txt')
 if not out.exists():subprocess.run(['pdftotext','-layout',str(p),str(out)],check=False)
print(versions)
