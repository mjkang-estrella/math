import sys,json,re,importlib.util
from pathlib import Path
L=Path(__file__).resolve().parents[1]; s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py'); m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
D=json.loads((L/'outputs/exact-records.json').read_text()); out={}
for i,d in D.items():
 p=next((L/'sources').glob(i+'-abs-*/body')); t=p.read_text(); versions=sorted(set(re.findall(r'\[v(\d+)\]',t)),key=int); a=d['record']['source_url'].split('/')[-1]; out[i]={'versions':versions,'doi':re.findall(r'https://doi.org/[^"<>\s]+',t),'journal':re.findall(r'journal-ref[^\n]*',t)}
 print(i,versions,out[i]['doi'],out[i]['journal'])
 if sys.argv[1]=='fetch' and 'arxiv' in d['record']['source_url']:
  for v in versions or ['1']: m.fetch(f'https://arxiv.org/html/{a}v{v}',f'{i}-v{v}-html')
(L/'outputs/version-inventory.json').write_text(json.dumps(out,indent=2))
