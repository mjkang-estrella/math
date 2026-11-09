import runpy,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];get=runpy.run_path(str(D/'scripts/fetch.py'))['get']
todo=[('omega-tree.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/65a253616c22829023b8ff1c09cf1d5e6a221cf6?recursive=1'),('upadhyay.html','https://arxiv.org/abs/2101.10612'),('hiroshima.html','https://arxiv.org/abs/1912.06357'),('code-public.html','https://probxiv.com/problems/on-strongly-walk-regular-graphs-triple-sum-sets-and-their-codes-3'),('partition-correction.pdf','https://arxiv.org/pdf/2011.08874v2')]
for key,url in todo:
 if (D/'sources'/f'{key}.receipt.json').exists():continue
 print(get((key,url)),flush=True)
