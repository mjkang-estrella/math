import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
for f in ['lascoux','eta','coprime','ew','cyclic']:
 r=json.loads((L/f'outputs/{f}.json').read_text())
 if f=='lascoux':print(f,{k:v for k,v in r.items() if k!='rows'})
 elif f=='eta':print(f,'rows',len(r['rows']),'inconsistent',[x for x in r['rows'] if not x['consistent']])
 elif f=='coprime':print(f,'last',r['rows'][-1])
 elif f=='ew':print(f,[(x['n'],x['fillings_examined'],x['equal']) for x in r['rows']])
 else:print(f,'printed_n',[x['n'] for x in r['printed_witness_checks']],'allzero',all(x['sum']=='0' and x['is_permutation'] for x in r['printed_witness_checks']),'extensions',len(r['four_cycle_extensions']))
pat=re.compile('Sabri|Vajnov|co.?rgc|EWTableau|EW.Tableau|CoprimeLabel|Hypertope|Lascoux|Pratt|Harer|Kolberg|MaoFan|RotationSymmetricBent|DominationDesign',re.I)
reg={}
for name in ['omega-d5','omega-problems']:
 p=L/f'sources/{name}.json';r=json.loads(p.read_text());hits=[x['path'] for x in r['tree'] if pat.search(x['path'])]
 reg[name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'tree_sha':r['sha'],'truncated':r.get('truncated'),'paths':len(r['tree']),'literal_topic_path_hits':hits}
print('registry',reg)
(L/'outputs/registry-complete-screen.json').write_text(json.dumps(reg,indent=2))
