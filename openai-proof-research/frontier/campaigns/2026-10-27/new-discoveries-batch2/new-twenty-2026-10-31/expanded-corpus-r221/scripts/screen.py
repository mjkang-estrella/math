import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1]
pat=re.compile(r'rowmotion|homomes|ising|unicellular|divisib|saxl|klein|suspension|blaschke|chromatic.*homolog|gluing.*poset|venn|one.?cross|colbourn|subsquare|sphere.*separat|polytope.*rigid|ultrametric|chi.?guard',re.I)
out={}
for p in (D/'sources').glob('*tree.json'):
 d=json.loads(p.read_text());hits=[x for x in d.get('tree',[]) if pat.search(x['path'])];out[p.name]={'truncated':d.get('truncated'),'hits':hits}
for p in (D/'sources').glob('pool-*'):
 if p.name.endswith(('.receipt.json','tree.json','head.json')):continue
 hits=[line for line in p.read_text().splitlines() if pat.search(line)]
 out[p.name]={'hits':hits}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
for k,v in out.items():
 print(k,'truncated',v.get('truncated'),'hits',len(v['hits']))
 for h in v['hits'][:70]:print(h['path'] if isinstance(h,dict) else h)
