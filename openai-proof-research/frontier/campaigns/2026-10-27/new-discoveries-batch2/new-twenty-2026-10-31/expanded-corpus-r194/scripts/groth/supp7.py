# Compute supports of Grothendieck polynomials for S_n layer by layer (memory-light); save supports of almost-vexillary non-vexillary perms.
import sys, json, pathlib, itertools, time
sys.path.insert(0,'')  # not used
n=int(sys.argv[1]); out=pathlib.Path(sys.argv[2])
exec(open(pathlib.Path(sys.argv[0]).with_name('common.py')).read())
t=time.time()
w0=tuple(range(n,0,-1)); layer={w0:{tuple(n-1-i for i in range(n)):1}}; S={}
maxterms=0
while layer:
    nxt={}
    for w,f in layer.items():
        maxterms=max(maxterms,len(f))
        if almost(w) and not vex(w): S[''.join(map(str,w))]=sorted(f)
        for i in range(n-1):
            if w[i]>w[i+1]:
                v=list(w); v[i],v[i+1]=v[i+1],v[i]; v=tuple(v)
                if v not in nxt: nxt[v]=dd(f,i)
    layer=nxt
out.write_text(json.dumps(S))
print('targets',len(S),'maxterms',maxterms,'secs',round(time.time()-t,1))
