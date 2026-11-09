# Cross-check certify_gen.Gamma (multiset recursion, Python) against famstates.cpp (positional, C++)
# on all families (blocked and free) of S(x,y,.) for r <= R.
import sys, subprocess
sys.argv=[sys.argv[0]]+sys.argv[1:]
import certify_gen as G
FS={'F':'*','T':'I','A':'O'}
def leg(s):
    return None if s=='-' else (int(s[:-1]), FS[s[-1]])
for (x,y,R) in [(1,5,120),(3,5,120),(4,7,120),(2,9,120),(5,6,100)]:
    out=subprocess.run(['./famstates',str(x),str(y),str(R)],capture_output=True,text=True).stdout
    n=bad=0
    for L in out.strip().split('\n'):
        head,vals=L.split(':'); lab,a,b,f=head.split()
        K=tuple(sorted(t for t in (leg(a),leg(b)) if t))
        s={'N':'n','I':'i','O':'o'}[lab]
        for r,v in enumerate(map(int,vals.split()),1):
            n+=1
            if G.Gamma(s,tuple(sorted(K+((r,FS[f]),))))!=v: bad+=1
    print((x,y),'compared',n,'mismatches',bad)
