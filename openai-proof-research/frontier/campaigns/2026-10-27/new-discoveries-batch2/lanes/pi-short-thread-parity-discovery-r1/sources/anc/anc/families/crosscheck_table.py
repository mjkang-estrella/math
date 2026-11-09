# Cross-check Table B (verify23.TABLE) against the independent positional C++ solver famstates.cpp
# output fs23_3000.txt (all 93 positional families of S(2,3,.), r = 1..3000).
import sys
sys.argv=[sys.argv[0]]
import verify23 as V
FS={'F':'*','T':'I','A':'O'}
def leg(s):
    if s=='-': return None
    return (int(s[:-1]), FS[s[-1]])
n=0; bad=0
for L in open('fs23_3000.txt'):
    head,vals=L.split(':'); lab,a,b,f=head.split(); vals=list(map(int,vals.split()))
    if f=='F': continue
    K=tuple(sorted(x for x in (leg(a),leg(b)) if x))
    kappa=({'N':'n','I':'i','O':'o'}[lab],K)
    for r,v in enumerate(vals,1):
        n+=1
        if V.closed(kappa,FS[f],r)!=v: bad+=1
print('compared',n,'values, mismatches',bad)
