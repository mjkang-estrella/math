import itertools, json
from pathlib import Path
edges=[(0,1),(0,6),(1,6),(2,3),(2,7),(3,7),(4,6),(4,7),(5,6),(5,7),(6,7)]
def graph(n,es):
    a=[0]*n
    for x,y in es: a[x]|=1<<y; a[y]|=1<<x
    return a
g=graph(8,edges)
me=[(v,8+i) for i,e in enumerate(edges) for v in e]
me += [(8+i,8+j) for i,e in enumerate(edges) for j,f in enumerate(edges) if i<j and set(e)&set(f)]
m=graph(19,me)
def mask(s): return sum(1<<i for i in s)
def dom(a,s):
    seen=s
    for i,nb in enumerate(a):
        if (s>>i)&1: seen|=nb
    return seen==(1<<len(a))-1
def conn(a,r,empty):
    if not r: return empty
    seen=r&-r; todo=seen
    while todo:
        bit=todo&-todo; todo-=bit
        new=a[bit.bit_length()-1]&r&~seen
        seen|=new; todo|=new
    return seen==r
def ocd(a,s,empty): return dom(a,s) and conn(a,((1<<len(a))-1)^s,empty)
def minimum(a,empty):
    for k in range(len(a)+1):
        ss=[list(s) for s in itertools.combinations(range(len(a)),k) if ocd(a,mask(s),empty)]
        if ss:return dict(value=k,count=len(ss),sets=ss)
    return None
out={}
for empty in [False,True]:
    out[str(empty)]={'G8':minimum(g,empty),'middle':minimum(m,empty)}
    assert out[str(empty)]['G8']['value']==out[str(empty)]['middle']['value']==4
    assert out[str(empty)]['G8']['count']==8 and out[str(empty)]['middle']['count']==2
assert len(me)==48 and len(set(me))==48
assert dom(g,mask([6,7])) and not conn(g,255^mask([6,7]),True)
assert not dom(g,mask([0]))
assert not dom(m,mask(range(8,11)))
assert ocd(g,mask([0,2,4,5]),False)
assert ocd(m,mask([8,11,14,17]),False)
out['order_size']={'G8':[8,len(edges)],'middle':[len(m),len(me)]}
out['negative_sets']={'G8_singleton_0':'not dominating','G8_hubs_6_7':'dominating, complement disconnected','middle_first_three_edges':'not dominating'}
# Independent certificate inventory and source scan. Remove nested comments and strings.
def stripped(s):
    o=[]; i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s[i:i+2]=='/-':depth+=1;i+=2
            elif s[i:i+2]=='-/':depth-=1;i+=2
            else:
                o.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            if s[i]=='\\':i+=2
            elif s[i]=='"':string=False;i+=1
            else:o.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s[i:i+2]=='/-':depth=1;i+=2
        elif s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j
        elif s[i]=='"':string=True;i+=1
        else:o.append(s[i]);i+=1
    assert depth==0 and not string
    return ''.join(o)
import re
root=Path(__file__).resolve().parents[1]
scans={}
for p in sorted((root/'extracted').glob('*.lean')):
    bad=re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b', stripped(p.read_text()))
    scans[p.name]=bad
assert not any(scans.values()),scans
s=(root/'extracted/MiddleSmall.lean').read_text()
certs=re.findall(r'theorem bad_(\d+) : ¬ IsOCD G8 (.*?) := by',s)
assert len(certs)==93 and [int(i) for i,_ in certs]==list(range(93))
sets=[]
for _,text in certs:
    b=text.split(':')[0]; vs=tuple(map(int,re.findall(r'\d+',b)))
    sets.append(vs)
assert set(sets)=={s for k in range(4) for s in itertools.combinations(range(8),k)}
out['certificate_inventory']={'count':93,'distinct':len(set(sets)),'covers_all_subsets_size_at_most_3':True}
out['source_scan']=scans
(root/'sanity.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
