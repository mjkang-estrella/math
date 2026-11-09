import sys
sys.dont_write_bytecode=True
import os,json,math,time
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from hnt import order,is_prime
HERE=os.path.dirname(os.path.abspath(__file__))
def scan(limit=5000000):
    start=time.monotonic();supply=json.load(open(os.path.join(HERE,'supply_B.json')))
    known={x[0] for x in supply}
    sieve=bytearray(b'\1')*(limit+1);sieve[:2]=b'\0\0'
    for p in range(2,math.isqrt(limit)+1):
        if sieve[p]:sieve[p*p::p]=b'\0'*((limit-p*p)//p+1)
    out=[]
    for p in range(11,limit+1,2):
        if not sieve[p] or p in known:continue
        n=p-1;fac={};q=2
        while q*q<=n:
            if n%q==0:
                fac[q]=0
                while n%q==0:n//=q;fac[q]+=1
            q+=1 if q==2 else 2
        if n>1:fac[n]=1
        d=order(10,p,fac)
        if d>3000:continue
        smooth=d
        for q in (2,3,5,7,11,13):
            while smooth%q==0:smooth//=q
        if smooth!=1:continue
        a,w=order(3,p,fac),order(7,p,fac);index=(p-1)//math.lcm(a,w)
        if index>1:out.append([p,d,a,w,index])
    json.dump({'limit':limit,'max_order':3000,'allowed_order_factors':[2,3,5,7,11,13],
        'seconds':time.monotonic()-start,'new_primes':out},open(os.path.join(HERE,'supply_scan.json'),'w'),indent=2)
    print('new',len(out),out,flush=True)
if __name__=='__main__':scan()
