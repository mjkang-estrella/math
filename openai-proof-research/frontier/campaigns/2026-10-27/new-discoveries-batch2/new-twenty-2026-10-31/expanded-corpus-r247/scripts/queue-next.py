import pathlib,json,re
L=pathlib.Path(__file__).resolve().parents[1];q=[]
for name,repo in [('openai','openai/math'),('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing')]:
 h=json.loads((L/'http'/f'{name}-head/body').read_text())['sha'];q.append((name+'-tree',f'https://api.github.com/repos/{repo}/git/trees/{h}?recursive=1'))
for r in json.loads((L/'reservation.json').read_text())['rows']:
 i=r['mathdb_id'];s=(L/'http'/f'{i}-abs/body').read_text();vs=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int)
 print(i,'versions',vs)
 for v in vs:q.append((f'{i}-pdf-v{v}',r['source_url'].replace('/abs/','/pdf/')+'v'+v))
(L/'queue-next.json').write_text(json.dumps(q))
