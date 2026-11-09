# For each (x,y), the family B(t)=Gamma(N;(x,F),(y,F),(t,delta)) and whether B(t)-t is eventually constant
import subprocess
H=400
print('x y | delta-independent? | B(t)-t eventually const c (from t0) | else period of B(t)-t')
for y in range(1,13):
    for x in range(1,y+1):
        out=subprocess.run(['./fsolve',str(x),str(y),str(H),'dump'],capture_output=True,text=True).stdout.splitlines()
        fam={}
        for line in out[1:]:
            head,vals=line.split(':'); t=head.split()
            key=tuple(int(t[i]) for i in (1,3,4,6,7,9))
            fam[key]=[None]+list(map(int,vals.split()))
        bi=fam[(0,x,0,y,0,1)]; bo=fam[(0,x,0,y,0,2)]
        same=bi==bo
        d=[None]+[bi[t]-t for t in range(1,H+1)]
        t0=H
        while t0>1 and d[t0-1]==d[H]: t0-=1
        if t0<H//2:
            desc=f'c={d[H]} from t0={t0}'
        else:
            p=next(p for p in (2,4,8,16,32,64) if all(d[t]==d[t+p] for t in range(H//2,H-p+1)))
            desc=f'not constant; B(t)-t periodic, period {p}, values {sorted(set(d[H//2:]))}'
        print(x,y,'|',same,'|',desc)
