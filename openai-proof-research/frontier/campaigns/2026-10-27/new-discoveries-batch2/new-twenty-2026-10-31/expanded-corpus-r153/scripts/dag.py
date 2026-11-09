import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];exec((L/'scripts/delta.py').read_text().split('out=[]')[0]);r=json.loads((L/'outputs/delta-trace-checked.json').read_text());seen=set()
def visit(T):
 if T in seen:return
 seen.add(T)
 for x in wyes(T):visit(tuple(map(tuple,red(list(map(list,T)),x))))
visit(tuple(map(tuple,r['original'])));states=sorted(seen,key=lambda x:(len(x),x));idx={s:i for i,s in enumerate(states)}
nodes=[{'graph':s,'children':[[x,idx[tuple(map(tuple,red(list(map(list,s)),x)))]] for x in wyes(s)]} for s in states]
(L/'outputs/pure-dag.json').write_text(json.dumps({'root':idx[tuple(map(tuple,r['original']))],'lower_bound':11,'nodes':nodes},separators=(',',':')))
print('DAG',len(nodes),'arcs',sum(len(v['children']) for v in nodes),'min order',min(map(len,states)))
