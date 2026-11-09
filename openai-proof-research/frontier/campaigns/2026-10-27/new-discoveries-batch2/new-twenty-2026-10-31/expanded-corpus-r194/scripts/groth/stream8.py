# Stream Grothendieck polynomials of S_n layer by layer; for targets (almost vexillary, not vexillary) whose
# index in a fixed order falls in residue class r mod m, run the one-per-column A search inline.
import sys, json, pathlib, itertools, time, zlib
exec(open(pathlib.Path(sys.argv[0]).with_name('common.py')).read())
src=open(pathlib.Path(sys.argv[0]).with_name('sbd.py')).read()
exec(src[src.index('def rothe('):src.index('G=groth_all(n)')])
n=int(sys.argv[1]); m=int(sys.argv[2]); r=int(sys.argv[3]); out=pathlib.Path(sys.argv[4]); budget=float(sys.argv[5])
t0=time.time(); w0=tuple(range(n,0,-1)); layer={w0:{tuple(n-1-i for i in range(n)):1}}
res=[]; ntarg=0; stopped=False
while layer and not stopped:
    nxt={}
    for w,f in layer.items():
        if almost(w) and not vex(w):
            ntarg+=1
            if zlib.crc32(bytes(w))%m==r:
                if time.time()-t0>budget: stopped=True; break
                D=rothe(w); supp=set(f); Dl=sorted(D); cols={}
                for s in Dl: cols.setdefault(s[1],[]).append(s)
                found=None; tried=0; capped=0
                for choice in itertools.product(*[[None]+c for c in cols.values()]):
                    A=frozenset(x for x in choice if x is not None); tried+=1
                    W=sbd_weights(D,A,n)
                    if W is None: capped+=1; continue
                    if W==supp: found=sorted(A); break
                res.append(dict(w=''.join(map(str,w)),len=len(D),supp=len(supp),found=found,tried=tried,capped=capped))
                if found is None: print('NO one-per-column A for',w,flush=True)
        for i in range(n-1):
            if w[i]>w[i+1]:
                v=list(w); v[i],v[i+1]=v[i+1],v[i]; v=tuple(v)
                if v not in nxt: nxt[v]=dd(f,i)
    layer=nxt
print('n',n,'class',r,'mod',m,'checked',len(res),'fail',sum(x['found'] is None for x in res),'stopped',stopped,'targets seen',ntarg,'secs',round(time.time()-t0,1))
out.write_text(json.dumps(res,indent=0))
