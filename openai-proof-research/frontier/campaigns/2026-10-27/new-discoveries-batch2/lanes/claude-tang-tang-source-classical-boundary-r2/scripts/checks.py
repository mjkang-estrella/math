"""Diagnostic-only numerical consistency checks (no proof value).
(a) Submitted density k(r) equals James (1.1) Lamperti ratio density at alpha=2/3 (symbolic identity; checked pointwise).
(b) Change of variables T=1/(1+R) maps k to Lamperti (1.4) density with mean parameter 1/2, index delta=2/3.
(c) Lamperti (3.17) Stieltjes transform, and James (2.6) at theta=0, against quadrature of the submitted measure.
(d) Submitted quantile r(u) inverts the CDF of k at sample points.
Writes JSON to argv[1]."""
import math, json, sys
a = 2/3; th = math.pi*a; s, c = math.sin(th), math.cos(th)
k = lambda r: s/math.pi * r**(a-1)/(1+2*r**a*c+r**(2*a))
james = lambda y: math.sin(math.pi*a)/math.pi * y**(a-1)/(y**(2*a)+2*y**a*math.cos(math.pi*a)+1)
d = a
def lamperti(t):  # (1.4) with ratio (1-alpha)/alpha = 1
    return math.sin(math.pi*d)/math.pi*(t**d*(1-t)**(d-1)+t**(d-1)*(1-t)**d)/(t**(2*d)+2*t**d*(1-t)**d*math.cos(math.pi*d)+(1-t)**(2*d))
out = {}
rs = [1e-4, 0.03, 0.5, 1.0, 2.7, 40.0, 1e4]
out['a_max_rel_diff_k_vs_james'] = max(abs(k(r)-james(r))/k(r) for r in rs)
# T=1/(1+R): density of T at t is k(r)*|dr/dt| with r=(1-t)/t, |dr/dt|=1/t^2
ts = [1e-3, 0.1, 0.3, 0.5, 0.77, 0.999]
out['b_max_rel_diff_pushforward_vs_lamperti'] = max(abs(k((1-t)/t)/t**2-lamperti(t))/lamperti(t) for t in ts)
# quadrature in v=r^a, v=tan(phi): dmu = (s/(pi a)) dv/(1+2vc+v^2)
N = 200000
def mu_int(f):
    h = (math.pi/2)/N; tot = 0.0
    for i in range(N):
        ph = (i+0.5)*h; v = math.tan(ph); dv = 1/math.cos(ph)**2
        tot += f(v**(1/a))*s/(math.pi*a)*dv/(1+2*v*c+v*v)
    return tot*h
out['c_total_mass'] = mu_int(lambda r: 1.0)
res = []
for z in [0.05, 0.4, 1.0, 3.0, 25.0]:
    lhs = mu_int(lambda r: z/(z+r))
    james26 = 1/(1+(1/z)**a)          # E[(1+lam R)^-1], lam=1/z
    # Lamperti (3.17): int_0^1 dG(t)/(t+u), T=1/(1+R)
    u = 0.7*z
    l317 = ((u+1)**(d-1)+u**(d-1))/((u+1)**d+u**d)
    q317 = mu_int(lambda r: 1/(1/(1+r)+u))
    res.append({'z': z, 'quad': lhs, 'target_z^a/(1+z^a)': z**a/(1+z**a), 'james_2.6_theta0': james26, 'u': u, 'lamperti_3.17': l317, 'quad_3.17': q317})
out['c_transforms'] = res
def cdf(r):
    return (math.atan((r**a+c)/s)-(math.pi/2-th))/th
rq = lambda u: (math.sin(th*u)/math.sin(th*(1-u)))**(1/a)
out['d_max_abs_cdf_of_quantile_minus_u'] = max(abs(cdf(rq(u))-u) for u in [0.001, 0.2, 0.5, 0.8, 0.999])
json.dump(out, open(sys.argv[1], 'w'), indent=1)
print(json.dumps(out, indent=1))
