from work import *
import itertools,collections
BASE='abcbabcbcacbcacabacabcbacabcabacacbcacbabcbcacbca'
def children(w):
 return sorted({w[:i]+w[i+k:] for k in range(1,len(w)//2+1) for i in range(len(w)-2*k+1) if w[i:i+k]==w[i+k:i+2*k]})
def closure(w,cap=45000):
 todo=[w]; edges={}
 while todo:
  v=todo.pop()
  if v in edges:continue
  edges[v]=children(v);todo.extend(c for c in edges[v] if c not in edges)
  if len(edges)>cap:raise RuntimeError('45000-state cap; incomplete, no count')
 roots={}
 for v in sorted(edges,key=len):roots[v]=set().union(*(roots[c] for c in edges[v])) if edges[v] else {v}
 return edges,roots
if sys.argv[1]=='dag':
 e,r=closure(BASE); terms=sorted(r[BASE]);idx={t:i for i,t in enumerate(terms)}
 masks={w:sum(1<<idx[t] for t in rr) for w,rr in r.items()}
 out={'word':BASE,'edges':e,'terminal_masks':{w:hex(m) for w,m in masks.items()},'terminals':terms}
 put('known81-dag.json',out)
 hist=collections.Counter(len(rr) for rr in r.values()); analysis=[]
 for w in sorted(e,key=lambda v:(-len(r[v]),-len(v),v)):
  if len(r[w])<79:continue
  ch=e[w]; full=masks[w]
  unique={c:(masks[c]&~(sum([],[]) if False else 0)) for c in []}
  indispensable={c:sorted(r[c]-set().union(*(r[d] for d in ch if d!=c))) for c in ch}
  pairs=[{'a':a,'b':b,'union':len(r[a]|r[b]),'intersection':len(r[a]&r[b])} for i,a in enumerate(ch) for b in ch[i+1:]]
  attainable={0}
  for c in ch:attainable|={m|masks[c] for m in list(attainable)}
  analysis.append({'word':w,'count':len(r[w]),'children':{c:len(r[c]) for c in ch},'indispensable':indispensable,'pairs':pairs,'all_subset_unions':len(attainable),'unions80':[hex(m) for m in sorted(attainable) if m.bit_count()==80]})
 put('dag-analysis.json',{'histogram':dict(sorted(hist.items())),'near80_nodes':analysis,'nodes80':[w for w in r if len(r[w])==80]})
 print('DAG',len(e),'hist',dict(sorted(hist.items())),'near',len(analysis),'unions80',sum(len(x['unions80']) for x in analysis))
elif sys.argv[1]=='grammar':
 # Every contiguous interval of the fixed 49-letter source. Shared memo avoids re-enumeration.
 memo={}; rows=[]
 def calc(w):
  if w not in memo:
   ch=children(w);memo[w]=set().union(*(calc(c) for c in ch)) if ch else {w}
  return memo[w]
 for i in range(len(BASE)):
  for j in range(i+1,len(BASE)+1):
   w=BASE[i:j];rr=calc(w);rows.append({'i':i,'j':j,'count':len(rr)})
   if len(rr)==80:put('witness.json',{'word':w,'terminals':sorted(rr)})
 put('interval-grammar.json',{'grammar':'BASE[i:j], 0<=i<j<=49','rows':rows,'memo_states':len(memo),'histogram':dict(sorted(collections.Counter(x['count'] for x in rows).items()))})
 print('intervals',len(rows),'states',len(memo),'max',max(x['count'] for x in rows),'80',sum(x['count']==80 for x in rows))
elif sys.argv[1]=='code':
 phi=dict(zip('abc',['abacabcbacabacbabc','abacabcbacbcacbabc','abacbcacbacabcbabc']))
 enc=lambda w:''.join(phi[c] for c in w)
 failures=[];trials=[]
 for n in range(1,8):
  for a in itertools.product('abc',repeat=n):
   w=''.join(a);v=enc(w);expected={enc(c) for c in children(w)};actual=set(children(v))
   if actual!=expected:
    failures.append({'input':w,'encoded':v,'expected_children':sorted(expected),'extra_children':sorted(actual-expected),'missing_children':sorted(expected-actual)})
   trials.append({'word':w,'children':len(actual),'extra':len(actual-expected)})
 put('code-reflection.json',{'property':'C(phi(w)) = phi(C(w))','map':phi,'trials':trials,'failures':failures})
 print('reflection trials',len(trials),'failures',len(failures),'first',failures[:1])
 # Shared ternary c as separator: complete closure for all binary square-free sides.
 binary=['a','b','ab','ba','aba','bab'];bad=[];good=[]
 for u,v in itertools.product(binary,repeat=2):
  e,r=closure(u+'c'+v);good.append({'u':u,'v':v,'count':len(r[u+'c'+v]),'states':len(e)})
 # Two occurrences permit cross-boundary reductions; shortest square-free-side counterexample.
 words=[''.join(x) for n in range(1,5) for x in itertools.product('abc',repeat=n) if not children(''.join(x))]
 for u,v in itertools.product(words,repeat=2):
  w=u+'c'+v;e,r=closure(w)
  if r[w]!={w}:bad.append({'u':u,'v':v,'word':w,'terminals':sorted(r[w])})
 put('separator-tests.json',{'absent_both_sides':good,'reuse_failures':bad[:30],'reuse_trials':len(words)**2})
 print('separator',len(good),'reuse trials',len(words)**2,'failed',len(bad))
elif sys.argv[1]=='union':
 d=json.loads((L/'known81-dag.json').read_text()); ch=d['edges'][BASE];m={w:int(s,16) for w,s in d['terminal_masks'].items()};terms=d['terminals'];rows=[]
 for bits in range(1<<len(ch)):
  union=0;selected=[]
  for i,c in enumerate(ch):
   if bits>>i&1:union|=m[c];selected.append(i)
  if union.bit_count()==80:rows.append({'branches':selected,'omitted_terminal':[t for i,t in enumerate(terms) if not union>>i&1][0]})
 minimal=[r for r in rows if not any(set(s['branches'])<set(r['branches']) for s in rows)]
 put('union80-branch-plans.json',{'children':ch,'all_plans':rows,'inclusion_minimal':minimal}); print('plans',len(rows),'minimal',minimal)
elif sys.argv[1]=='sync':
 codes=['abacabcbacabacbabc','abacabcbacbcacbabc','abacbcacbacabcbabc'];q=len(codes[0]);bad=[]
 for a,b,c in itertools.product(codes,repeat=3):
  for r in range(1,q):
   if (a+b)[r:r+q]==c:bad.append([a,b,c,r])
 splits=[{'r':r,'prefix_injective':len({c[:r] for c in codes})==3,'suffix_injective':len({c[r:] for c in codes})==3} for r in range(1,q)]
 put('synchronization.json',{'q':q,'offblock_occurrences':bad,'splits':splits})
 print('offblock',bad,'bad_splits',[s for s in splits if not(s['prefix_injective'] or s['suffix_injective'])])
elif sys.argv[1]=='extend':
 old=['abacabcbacabacbabc','abacabcbacbcacbabc','abacbcacbacabcbabc'];q=18
 words=['']
 for n in range(q):words=[w+c for w in words for c in 'abc' if all((w+c)[-2*k:-k]!=(w+c)[-k:] for k in range(1,(len(w)+1)//2+1))]
 survivors=[];hist=collections.Counter();rejections=[]
 for d in words:
  if d in old:continue
  codes=old+[d]
  if any(len({c[:r] for c in codes})<4 and len({c[r:] for c in codes})<4 for r in range(1,q)):hist['split_fail']+=1;rejections.append({'code':d,'reason':'split injectivity certificate fails'});continue
  if any((a+b)[r:r+q] in codes for a,b in itertools.product(codes,repeat=2) for r in range(1,q)):hist['sync_fail']+=1;rejections.append({'code':d,'reason':'offblock codeword occurs'});continue
  # Necessary one-step reflection on pairs, then triples; a survivor is not a theorem yet.
  failed=False
  for n in [2,3]:
   for t in itertools.product(range(4),repeat=n):
    if 3 not in t:continue
    w=''.join(str(i) for i in t);enc=lambda s:''.join(codes[int(i)] for i in s)
    if set(children(enc(w)))!={enc(c) for c in children(w)}:
     failed=True;hist['length'+str(n)+'_fail']+=1;rejections.append({'code':d,'reason':'one step reflection fails','input':w,'extra_children':sorted(set(children(enc(w)))-{enc(c) for c in children(w)})});break
   if failed:break
  if not failed:survivors.append(d)
 put('fourth-code-extension.json',{'universe':'all square-free ternary words of length18','universe_size':len(words),'original_codes':old,'filters':dict(hist),'survivors_pairs_triples':survivors,'rejections':rejections})
 print('fourth codes',len(words),dict(hist),'survivors',survivors)
elif sys.argv[1]=='contexts':
 ctx=['']+list('abc')+[''.join(t) for t in itertools.product('abc',repeat=2) if t[0]!=t[1]];rows=[]
 for u,v in itertools.product(ctx,repeat=2):
  w=u+BASE+v;e,r=closure(w);rr=r[w]
  rows.append({'prefix':u,'suffix':v,'states':len(e),'count':len(rr),'root_children':{c:len(r[c]) for c in e[w]}})
  if len(rr)==80:put('witness.json',{'word':w,'terminals':sorted(rr),'edges':e})
  put('context-grammar.json',{'grammar':'u BASE v, u,v ternary square-free of length<=2 including empty','complete':len(rows)==100,'rows':rows})
 print('contexts',len(rows),'80',sum(x['count']==80 for x in rows),'counts',sorted({x['count'] for x in rows}))
