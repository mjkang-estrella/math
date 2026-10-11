import sys,json
from pathlib import Path
from collections import Counter
sys.path.insert(0,str(Path(__file__).resolve().parent))
from toolkit import *
root=Path(__file__).resolve().parents[3]
a=json.loads((Path(__file__).parent/'audit-attempt-02.json').read_text());graphs=list(json.loads((root/'frontier/experiments/i166_affine_span_braces/bracegen-graphs.json').read_text())['bfs'].values());gg={g['history']:g for g in graphs}
out=[];hist=Counter()
for i in a['first_test_order']+[i for i in range(636) if i not in a['first_test_order']]:
 z=a['rows'][i];es=list(map(tuple,z['parent_edges']));u,v,x,y,*_=z['labels'];cs={k:[frozenset(map(tuple,c)) for c in cc] for k,cc in z['classes'].items()};sur=cs['N10']+cs['N01']+cs['N11'];L=differences(sur,es);V=differences(cs['N00'],es);U=sum((differences(cs[k],es) for k in ['Pux','Pvy','D11']),[])
 face=gg[z['history']]['faces'][z['step'][0]];square=len(face)==4
 if square:
  s=[int(e in [edge(u,v),edge(x,y)])-int(e in [edge(u,x),edge(v,y)]) for e in es]
  r=sub(vec(cs['N00'][0],es),vec(sur[0],es))
  assert all(set(cs[k])=={c-set(rem) for c in cs['N00']} for k,rem in [('Pux',[edge(u,x)]),('Pvy',[edge(v,y)]),('D11',[edge(u,x),edge(v,y)])])
  lr=rank(L+V);s_in=rank(L+V+[s])==lr
  co=[]
  for num in range(-8,9):
   for den in [1,2,3]:
    if rank_integer(L+V+[[den*x-num*y for x,y in zip(s,r)]])==lr:co.append(str(Fraction(num,den)))
  ss={'index':i,'face_length':4,'l':z['l'],'t':z['t'],'eta':z['eta'],'s_in':s_in,'s_over_r':sorted(set(co))}
 else:ss={'index':i,'face_length':len(face),'l':z['l'],'t':z['t'],'eta':z['eta']}
 hist[str((square,z['l'],z['t'],z['eta']))]+=1;out.append(ss)
print(json.dumps({'histogram':dict(hist),'rows':out},sort_keys=True,indent=2))
