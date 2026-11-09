import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1]
for key in ['leanpool','openai','omega']:
 p=D/'sources'/f'{key}-tree.json'
 if not p.exists():continue
 j=json.loads(p.read_text()); paths=[x['path'] for x in j.get('tree',[])];print(key,'paths',len(paths),'truncated',j.get('truncated'));print('\n'.join(p for p in paths if re.search(r'projects.yml|candidates/|Almkvist|Restraint|Entringer|BuildingNim|Rothe|PowerDom|Venn|Divisibility',p,re.I))[:5500])
j=json.loads((D.parent/'ledger.json').read_text())
def walk(x,path=''):
 if isinstance(x,dict):
  for k,v in x.items():walk(v,path+'/'+k)
 elif isinstance(x,list):
  for k,v in enumerate(x):walk(v,path+'/'+str(k))
 elif any(str(i) in str(x) for i in [334721,322962]):print('ledger',path,str(x)[:500])
walk(j)
