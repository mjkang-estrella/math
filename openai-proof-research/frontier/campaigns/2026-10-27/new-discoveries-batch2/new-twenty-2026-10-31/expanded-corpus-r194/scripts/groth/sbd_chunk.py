import sys, json, pathlib, itertools, time
exec(open(pathlib.Path(sys.argv[0]).with_name('common.py')).read())
src=open(pathlib.Path(sys.argv[0]).with_name('sbd.py')).read()
exec(src[src.index('def rothe('):src.index('G=groth_all(n)')])
S=json.load(open(sys.argv[1])); lo,hi=int(sys.argv[2]),int(sys.argv[3]); out=pathlib.Path(sys.argv[4]); budget=float(sys.argv[5]) if len(sys.argv)>5 else 85
keys=sorted(S)[lo:hi]; res=[]; t0=time.time()
for k in keys:
    if time.time()-t0>budget: print('BUDGET STOP at',k); break
    w=tuple(int(c) for c in k); n=len(w); D=rothe(w); supp=set(map(tuple,S[k])); Dl=sorted(D)
    cols={}
    for s in Dl: cols.setdefault(s[1],[]).append(s)
    found=None; tried=0; capped=0
    for choice in itertools.product(*[[None]+c for c in cols.values()]):
        A=frozenset(x for x in choice if x is not None); tried+=1
        W=sbd_weights(D,A,n)
        if W is None: capped+=1; continue
        if W==supp: found=sorted(A); break
    res.append(dict(w=k,len=len(D),supp=len(supp),found=found,tried=tried,capped=capped,stage='one-per-column'))
    if found is None: print('NO one-per-column A for',k,len(D),'tried',tried,'capped',capped,flush=True)
print('chunk',lo,hi,'done',len(res),'fail',sum(r['found'] is None for r in res),'secs',round(time.time()-t0,1))
out.write_text(json.dumps(res,indent=0))
