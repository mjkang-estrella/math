import sys,subprocess
from lemmas import *
H=int(sys.argv[1]); ys=list(map(int,sys.argv[2:]))
tot=0; bad=0
for y in ys:
    out=subprocess.run(['./fsolve','1',str(y),str(H),'dump'],capture_output=True,text=True).stdout.splitlines()
    g=list(map(int,out[0].split()))
    for z in range(y+2,H+1):
        tot+=1
        if g[z-1]!=gform(y,z): bad+=1; print('THM fail',y,z)
    for line in out[1:]:
        head,vals=line.split(':'); t=list(map(int,head.split()[1::2] if False else [head.split()[i] for i in (1,3,4,6,7,9)]))
        s,xh,xf,yh,yf,phi=t
        v=[None]+list(map(int,vals.split()))
        for h in range(1,H+1):
            exp=None
            if s in (1,2):
                # O-centre = I-centre with all far ends flipped
                fl=(lambda d:d) if s==1 else flip
                if xh==1 and yh==0:      # (I;(1,F),(h,phi))
                    exp=L2(h,fl(phi))
                elif xh==0 and yh>0 and yf!=F and phi!=F:
                    exp=L1(yh,fl(yf),h,fl(phi))
                elif xh==0 and yh==y and yf==F and phi!=F:
                    exp=L3(y,h,fl(phi))
            else:
                if yf!=F and phi!=F: exp=L4(yh,yf,h,phi)
                elif yh==y and yf==F and phi!=F: exp=L5(y,h)
            if exp is not None:
                tot+=1
                if v[h]!=exp:
                    bad+=1
                    if bad<20: print('fail',y,(s,xh,xf,yh,yf,phi),h,v[h],exp)
print('checked',tot,'bad',bad)
