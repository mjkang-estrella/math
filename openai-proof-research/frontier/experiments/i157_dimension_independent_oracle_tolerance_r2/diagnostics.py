"""New bounded examples only; not a universal correctness or contribution gate."""
from fractions import Fraction as F
import math
def run():
    k=[F(1,3),F(2,3)];e=[F(3,4),F(1,4)]
    L=[[F(1,5),F(4,5)],[F(2,7),F(5,7)]]
    joint=[(k[i]*L[i][j],e[i]*L[i][j]) for i in range(2) for j in range(2)]
    tv=sum(abs(a-b) for a,b in joint)/2
    assert tv==sum(abs(a-b) for a,b in zip(k,e))/2
    for i in range(2):
        for j in range(2):assert k[i]*L[i][j]/(e[i]*L[i][j])==k[i]/e[i]
    kl=lambda pairs:sum(float(a)*math.log(float(a/b)) for a,b in pairs)
    assert abs(kl(joint)-kl(zip(k,e)))<1e-14
    # Actual terminal formulas with g(x)=lambda*x; no abstract tree advertised as compiler.
    terminal=0
    for r in [F(1),F(1,2),F(1,16)]:
        lam=F(1,10);u=F(1,100)
        for x in [F(-3),F(0),F(5)]:
            for seed in [F(-20),F(0),F(100)]:
                for sign in [-1,1]:
                    exact=lam*(x+r*seed);noisy=exact+sign*u
                    assert abs(noisy-exact)==u
                    assert abs((seed-r*noisy)-(seed-r*exact))==r*u
                    terminal+=1
    schedules=[]
    for m in [1,2,4,16,64]:
        h=F(1,m);q=1/(1+h);a0=F(3);a=a0;energy=F(0)
        for j in range(m):
            theta=F(1,m-j)
            assert a==q**j*F(m-j,m)*a0
            energy+=q*q/(2*h)*theta*theta*a*a
            a=q*(1-theta)*a
        assert a==0 and energy<=a0*a0/(2*h*m)
        schedules.append({'m':m,'energy':str(energy),'upper':str(a0*a0/(2*h*m))})
    # Height domination at the worst permitted absorption alpha=1/2.
    C=F(2);l=p=F(1)
    for height in range(1,5):
        lp=8*C*C*l*(1+l);pp=8*C*C*p*(1+l)
        assert 2*C*l+2*C*C*l*l<=lp
        assert C*p*(2+2*C*l)<=pp
        l,p=lp,pp
    return dict(status='PASS',joint_state_TV=str(tv),joint_state_KL=kl(joint),actual_terminal_adversarial_cases=terminal,regularization_schedules=schedules,height_levels=4,scope='Finite examples only. No complete compiler simulation, universal proof, contribution, acceptance, or completion of unread obligations.')
