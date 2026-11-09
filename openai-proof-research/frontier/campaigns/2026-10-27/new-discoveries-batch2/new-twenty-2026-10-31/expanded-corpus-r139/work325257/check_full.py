# Full P_n for n in [a,b]: check (f) [even n>=20: sum|c| == P_n(-1)], record P_n(-1) for (e),
# sign-pattern data relevant to (b),(c). Prints one JSON line per n.
import sys, json, time, pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent)); from tatami import P
a,b=int(sys.argv[1]),int(sys.argv[2]); step=int(sys.argv[3]) if len(sys.argv)>3 else 1
for n in range(a,b+1,step):
    t=time.time(); p=P(n)
    pm1=sum(c if k%2==0 else -c for k,c in enumerate(p)); ab=sum(abs(c) for c in p)
    # (c)/(b) helpers: sign changes of P(x) (Descartes, x>0) and of P(-x)
    def sc(q):
        s=[x for x in q if x]; return sum(1 for u,v in zip(s,s[1:]) if (u>0)!=(v>0))
    neg=[c if k%2==0 else -c for k,c in enumerate(p)]
    print(json.dumps({'n':n,'deg':len(p)-1,'P(-1)':pm1,'abs_sum':ab,'f_holds':(ab==pm1) if n%2==0 else None,
        'desc_pos':sc(p),'desc_neg':sc(neg),'sec':round(time.time()-t,2)}),flush=True)
