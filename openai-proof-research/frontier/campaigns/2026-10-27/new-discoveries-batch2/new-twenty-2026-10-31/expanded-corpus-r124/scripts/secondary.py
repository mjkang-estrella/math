import runpy,pathlib,json,re,concurrent.futures
D=pathlib.Path(__file__).resolve().parents[1];get=runpy.run_path(str(D/'scripts/fetch.py'))['get']
for a in ['2101.10612','1907.10836']:
 print(get((a+'.html','https://arxiv.org/abs/'+a)),flush=True)
 p=D/'sources'/f'{a}.html'
 if p.exists():
  for v in sorted(set(re.findall(a+r'v\d+',p.read_text()))):print(get((v+'.pdf','https://arxiv.org/pdf/'+v)),flush=True)
print(get(('code-public.html','https://probxiv.com/problems/on-strongly-walk-regular-graphs-triple-sum-sets-and-their-codes-3')),flush=True)
