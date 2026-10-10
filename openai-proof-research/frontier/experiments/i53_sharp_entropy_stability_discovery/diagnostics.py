"""Read-only finite diagnostics for I53. No test substitutes for the proof."""
from fractions import Fraction as Q
from itertools import product, permutations
import hashlib
import json
import math
import random


def run():
    rng = random.Random(530091)
    counts = {}

    def check(name, condition):
        assert condition, name
        counts[name] = counts.get(name, 0) + 1

    def matmul(a, b):
        return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]

    def sub(a, b):
        return [[x-y for x, y in zip(r, s)] for r, s in zip(a, b)]

    def comm(a, b):
        return sub(matmul(a, b), matmul(b, a))

    def squares(xs):
        d = len(xs[0])
        return [[sum(matmul(a, a)[i][j] for a in xs) for j in range(d)] for i in range(d)]

    def norm2(t):
        if isinstance(t, list):
            return sum(norm2(x) for x in t)
        return t*t

    for d in range(2, 5):
        for trial in range(8):
            xs = []
            for r in range(d):
                a = [[Q(rng.randrange(-5, 6), 7) for _ in range(d)] for _ in range(d)]
                xs.append([[a[i][j]+a[j][i] for j in range(d)] for i in range(d)])
            s = [[[xs[r][i][j]-xs[j][i][r] for i in range(d)] for j in range(d)] for r in range(d)]
            for r, j, t, i in product(range(d), repeat=4):
                jet = (matmul(xs[r], xs[t])[i][j]+matmul(xs[t], xs[r])[i][j]
                       -matmul(xs[j], xs[t])[i][r]-matmul(xs[t], xs[j])[i][r])
                rebuilt = comm(xs[r], xs[j])[i][t] + sum(
                    xs[r][i][k]*s[t][j][k]-xs[j][i][k]*s[t][r][k]
                    +xs[t][i][k]*s[r][j][k] for k in range(d))
                check('jet_commutator_identity', jet == rebuilt)
            tensor = [[[sum(xs[c][a][b] for a,b,c in permutations((i,j,r)))/6
                        for r in range(d)] for j in range(d)] for i in range(d)]
            for i,j,r in product(range(d), repeat=3):
                check('full_symmetrization', tensor[i][j][r] == tensor[r][i][j])
            # Rational Householder matrix; rotate all three slots, not just slices.
            v = [Q(i+1) for i in range(d)]
            vv = sum(x*x for x in v)
            u = [[Q(i==j)-2*v[i]*v[j]/vv for j in range(d)] for i in range(d)]
            rot = [[[sum(u[a][i]*u[b][j]*u[c][r]*tensor[a][b][c]
                         for a,b,c in product(range(d), repeat=3))
                     for r in range(d)] for j in range(d)] for i in range(d)]
            check('rotation_tensor_norm', norm2(rot) == norm2(tensor))
            tx = [[[tensor[i][j][r] for j in range(d)] for i in range(d)] for r in range(d)]
            rx = [[[rot[i][j][r] for j in range(d)] for i in range(d)] for r in range(d)]
            check('rotation_commutator_array', sum(norm2(comm(a,b)) for a in tx for b in tx)
                  == sum(norm2(comm(a,b)) for a in rx for b in rx))
            check('rotation_B', squares(rx) == matmul(matmul(u, squares(tx)), u))

    # Deflation identities for stationary vectors, with arbitrary complement tensor.
    for d in range(2, 6):
        for trial in range(5):
            t = [[[Q(0) for _ in range(d)] for _ in range(d)] for _ in range(d)]
            t[0][0][0] = Q(1)
            for i in range(1,d):
                for j in range(i,d):
                    value = Q(rng.randrange(-3,4), 10**5)
                    for a,b,c in set(permutations((0,i,j))): t[a][b][c] = value
            for i in range(1,d):
                for j in range(i,d):
                    for k in range(j,d):
                        value = Q(rng.randrange(-4,5),11)
                        for a,b,c in set(permutations((i,j,k))): t[a][b][c] = value
            xs = [[[t[i][j][r] for j in range(d)] for i in range(d)] for r in range(d)]
            h = [[t[0][i][j] for j in range(1,d)] for i in range(1,d)]
            ys = [[row[1:] for row in a[1:]] for a in xs[1:]]
            b, bp, h2 = squares(xs), squares(ys), matmul(h,h)
            check('deflation_B', all(b[i+1][j+1] == bp[i][j]+2*h2[i][j]
                                    for i,j in product(range(d-1),repeat=2)))
            for a,b0 in product(range(d-1),repeat=2):
                ca, cb = comm(xs[a+1],xs[b0+1]), comm(ys[a],ys[b0])
                check('deflation_commutator', all(ca[i+1][j+1] == cb[i][j]
                    +h[i][a]*h[j][b0]-h[i][b0]*h[j][a]
                    for i,j in product(range(d-1),repeat=2)))
            xv2 = sub(matmul(xs[0],xs[0]), xs[0])
            check('idempotent_commutator', all(xv2[i][j] == comm(xs[0],xs[j])[i][0]
                                             for i,j in product(range(d),repeat=2)))
            kept = Q(1)+norm2([[[t[i][j][k] for k in range(1,d)]
                               for j in range(1,d)] for i in range(1,d)])
            check('discarded_tensor_norm', norm2(t)-kept == 3*norm2(h))

    for m in list(range(1,31))+[50,100,500,1000]:
        eta = Q(1, 10**6*m**4)
        check('induction_budget', 256*m*m*eta <= 1)
        check('coarse_c_positive', 1-2*eta-400*m**3*(2*eta)**2 >= Q(1,4))
        check('c_rounding', 16*m*2*eta <= 1)
        check('final_tensor_constant', 208*m*m < (20*m)**2)
    for a in [Q(1,2),Q(1,10),Q(1,100),Q(1,1000)]:
        mean = (1-a*a)/(1+a)
        moment2 = 2*(1+a**3)/(1+a)
        check('asymmetric_laplace_mean', mean == 1-a)
        check('asymmetric_laplace_variance', moment2-mean*mean == 1+a*a)
    for m in range(2,101):
        exponent=Q(1,m+6)
        check('mollification_exponent', 1-Q(m+4,m+6) == 2*exponent)
    check('weight_half_interval', Q(117,320000)>Q(1,10000))
    check('weight_core', Q(117,86000)>Q(1,1000))

    # Exact commuting/nonintegrable warning: X1=I, X2=0.
    i2=[[Q(1),Q(0)],[Q(0),Q(1)]]; z2=[[Q(0),Q(0)],[Q(0),Q(0)]]
    check('commuting_not_compatible', norm2(comm(i2,z2))==0 and squares([i2,z2])==i2 and i2[1][1]!=z2[1][0])
    # Known global maximizing example p(x,y)=x^3+3 a x y^2, 0<a<1/3.
    # On the unit circle this is (1-3a)x^3+3ax, strictly increasing in x.
    cubic=[]
    for a in [Q(1,10),Q(1,100),Q(1,1000),Q(1,10000)]:
        check('known_cubic_max', 1-3*a>0 and a>0 and a<Q(1,2))
        check('quadratic_restriction_cost', (2*a*a)**2 == 4*a**4)
        cubic.append({'a':str(a),'c':'1','H':str(a),'commutator_entry':str(a*a-a),
                      'B_restriction_correction':str(2*a*a),'stationary_complement_gap':str(1-a)})

    def softplus(x): return max(x,0)+math.log1p(math.exp(-abs(x)))
    def integrate(fn,n):
        a,b=-50.0,50.0; h=(b-a)/n
        return h/3*math.fsum((1 if k in (0,n) else 4 if k%2 else 2)*fn(a+k*h) for k in range(n+1))
    def law_case(kind,param,n):
        if kind=='truncated_exp':
            tail=math.exp(-param); mean=1-param*tail/(1-tail)
            var=1-param*param*tail/(1-tail)**2
            gap=1-param*tail/(1-tail)+math.log1p(-tail)-1-.5*math.log(var)
            def quant(t): return softplus(t)-softplus(t-param)
        else:
            mean=1-param;var=1+param*param
            gap=math.log1p(param)-.5*math.log1p(param*param)
            def quant(t):
                logu=-softplus(-t)
                return param*(logu+math.log1p(param)-math.log(param)) if logu<math.log(param/(1+param)) else softplus(t)-math.log1p(param)
        def integrand(t,sign):
            ex=math.exp(-abs(t));w=ex/(1+ex)**2
            ref=softplus(t)-1 if sign==1 else 1-softplus(-t)
            return w*((quant(t)-mean)/math.sqrt(var)-ref)**2
        return gap,[integrate(lambda t:integrand(t,sign),n) for sign in [1,-1]]
    laws=[]
    for kind,pars in [('truncated_exp',[2,4,8,12,16]),('asymmetric_laplace',[.5,.1,.01,.001])]:
        for param in pars:
            gap,coarse=law_case(kind,param,6000);_,fine=law_case(kind,param,12000)
            check('law_positive_gap',gap>0)
            check('law_quadrature_consistency',max(abs(a-b) for a,b in zip(coarse,fine))<2e-6)
            laws.append({'kind':kind,'parameter':param,'gap':gap,'W2_squared_signs':fine,
                         'two_resolution_difference':max(abs(a-b) for a,b in zip(coarse,fine))})
    inverse=[]
    for r in [2,4,6,8]:
        q=math.exp(-r*r/2)/math.sqrt(2*math.pi)/(math.erfc(-r/math.sqrt(2))/2)
        inverse.append({'R':r,'inverse_q_derivative':1/(q*(q+r))})
    def omega(lam):return 3*(lam-1)**2/(37+3*lam)*(.15+.49*37/(37+3*lam))*min(.13,1.28/math.sqrt(lam))
    spikes=[{'m':m,'lambda':m**1.5,'normalized_slack':omega(m**1.5)/m,
             'normalized_trace_B':(m-1+m**1.5)/m} for m in [10,100,1000,10000,1000000]]
    return {'status':'PASS finite diagnostics; not a universal proof','assertions':counts,
            'total_assertions':sum(counts.values()),'cubic_known_maximum':cubic,'actual_laws':laws,
            'inverse_q_nonuniformity':inverse,'abstract_matrix_spikes_not_law_counterexamples':spikes,
            'quadrature':'Simpson on logistic quantiles t in [-50,50], N=6000 and 12000; numerical only'}


if __name__ == '__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
