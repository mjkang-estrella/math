# Level-by-level (by number of elements) closure search, same CSP and pruning facts as orderable_binary_search.py,
# with isomorphism reduction under coordinate permutations (these fix the standard basis), and resumable checkpoints.
# State: level = all canonical classes (non-basis point tuples) of orderable simple binary rank-r matroids containing the
# standard basis, of the current size, without a spanning circuit; nxt = partial next level; pos = processed index.
import sys, itertools, json, time, os
src=open(sys.path[0]+'/orderable_binary_search.py').read().split('t=time.time()')[0]
r=int(sys.argv[1]); MAXM=int(sys.argv[2]); BUDGET=float(sys.argv[3]); CK=sys.argv[4] if len(sys.argv)>4 else None
_B=BUDGET; sys.argv=['x',str(r),str(MAXM),'0']; exec(src); BUDGET=_B
exec(open(sys.path[0]+'/orderable_fast.py').read()); orderable=orderable_fast  # cross-checked in orderable_fast_selftest.py
perms=list(itertools.permutations(range(r)))
def pv(p,v): return sum(((v>>i)&1)<<p[i] for i in range(r))
def canon(S): return min(tuple(sorted(pv(p,v) for v in S)) for p in perms)
st={'level':[[]],'size':r,'pos':0,'nxt':[],'hist':{},'stats':{'checked':0,'nonorderable':0,'spanning':0},'cands':[]}
if CK and os.path.exists(CK): st=json.load(open(CK))
t=time.time(); out_of_time=False
while st['level'] and st['size']<MAXM:
    level=sorted(tuple(x) for x in st['level']); nxt=set(tuple(x) for x in st['nxt'])
    while st['pos']<len(level):
        if time.time()-t>BUDGET: out_of_time=True; break
        S=level[st['pos']]
        for q in others:
            if time.time()-t>BUDGET: out_of_time=True; break
            if q in S: continue
            T=canon(S+(q,))
            if T in nxt: continue
            vecs=basis+list(T); circ=circuits(vecs); st['stats']['checked']+=1
            if has_spanning_circuit(circ,r): st['stats']['spanning']+=1; continue
            if not orderable(len(vecs),circ): st['stats']['nonorderable']+=1; continue
            nxt.add(T)
            if len(vecs)>=r+3 and connectivity3(vecs): st['cands'].append(vecs)
        if out_of_time: break   # S only partially processed: redo it next time (nxt keeps what was found)
        st['pos']+=1
    st['nxt']=sorted(nxt)
    if out_of_time: break
    st['size']+=1; st['hist'][str(st['size'])]=len(nxt); st['level']=st['nxt']; st['nxt']=[]; st['pos']=0
complete = not out_of_time and (not st['level'] or st['size']>=MAXM)
if CK: json.dump(st,open(CK,'w'))
print(json.dumps({'rank':r,'max_elements':MAXM,'complete':complete,'current_size':st['size'],'pos':st['pos'],'level_len':len(st['level']),'classes_per_size':st['hist'],**st['stats'],'num_3connected_orderable_without_spanning_circuit':len(st['cands']),'examples':st['cands'][:5],'secs':round(time.time()-t,1)}))
