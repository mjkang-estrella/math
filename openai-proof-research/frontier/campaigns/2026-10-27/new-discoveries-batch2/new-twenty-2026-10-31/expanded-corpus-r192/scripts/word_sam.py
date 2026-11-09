import pathlib,json,random,sys,runpy
D=pathlib.Path(__file__).resolve().parents[1]
# Same closure implementation as words.py, without running its search.
src=(D/'scripts/words.py').read_text();ns={};exec(src[src.index('def close('):src.index('best=(0,None)')],ns);close=ns['close']
def complexity(s):
 nxt=[{}];link=[-1];length=[0];last=0
 for c in s:
  cur=len(nxt);nxt.append({});length.append(length[last]+1);link.append(0);p=last
  while p>=0 and c not in nxt[p]:nxt[p][c]=cur;p=link[p]
  if p>=0:
   q=nxt[p][c]
   if length[p]+1==length[q]:link[cur]=q
   else:
    clone=len(nxt);nxt.append(nxt[q].copy());length.append(length[p]+1);link.append(link[q]);
    while p>=0 and nxt[p].get(c)==q:nxt[p][c]=clone;p=link[p]
    link[q]=link[cur]=clone
  last=cur
 diff=[0]*(len(s)+2)
 for v in range(1,len(nxt)):diff[length[link[v]]+1]+=1;diff[length[v]+1]-=1
 c=0;best=(0,0,0)
 for n in range(1,len(s)+1):
  c+=diff[n]
  if c/n>best[0]:best=(c/n,n,c)
 return best
rng=random.Random(19201);seed=json.loads((D/'outputs/words-random.json').read_text())['best_ratio'][1]['directive'];best=(0,None);rows=[]
for j in range(600):
 dirs=[list(x) for x in (seed if j<400 else [(str(rng.randrange(2)),rng.randrange(2)) for _ in range(20)])]
 if j:
  for _ in range(1+j%3):
   k=rng.randrange(len(dirs));dirs[k]=[str(rng.randrange(2)),rng.randrange(2)]
 w=''
 for b,e in dirs:
  w=close(w+b,e)
  if len(w)>65536:break
 z=complexity(w);row={'trial':j,'directive':dirs,'prefix_length':len(w),'ratio':z[0],'n':z[1],'factor_count':z[2]}
 if z[0]>best[0]:best=(z[0],row);print('BEST',json.dumps(row),flush=True)
 if z[0]>5.8 and j<400:seed=dirs
 if z[0]>=6:print('COUNTEREXAMPLE',json.dumps(row),flush=True);rows.append(row);break
 if j%10==0:(D/'outputs/word-sam.json').write_text(json.dumps({'completed':j+1,'best':best,'counterexamples':rows,'method':'All factor lengths via suffix automaton; finite prefixes give lower bounds only.'},indent=2))
(D/'outputs/word-sam.json').write_text(json.dumps({'completed':j+1,'best':best,'counterexamples':rows},indent=2))
