from pathlib import Path
import json
import resource
import mpmath as mp

resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2, 512 * 1024**2))
mp.mp.dps = 30

# Tanh-sinh (double exponential) nodes on (0,1): robust to endpoint singularities
# such as s^(c-1) with c<1, v^(p-1) with p<1, and w_b(y)=[y(1-y)]^(b-1) with b<1.
# x is formed by the cancellation-free identity (1+tanh(sh))/2 = 1/(1+exp(-2sh)).
# Note: beta means with a shape parameter p<=0.05 concentrate so extremely near an
# endpoint (v ~ e^{-const/p}) that no fixed-depth quadrature resolves them; such
# parameters are excluded here (the public Lean proof compares the means
# analytically and has no such limitation).


def make_nodes(step, rng):
    # Each node carries x and the EXACT 1-x (as 1/(1+exp(+2sh))), since x itself
    # rounds catastrophically near 1 at finite dps and the beta weights need
    # (1-x)^(q-1) to full precision.
    nodes = []
    for j in range(-rng, rng + 1):
        t = mp.mpf(j) * step
        sh = mp.pi / 2 * mp.sinh(t)
        x = 1 / (1 + mp.exp(-2 * sh))
        omx = 1 / (1 + mp.exp(2 * sh))
        w = (mp.pi / 4) * mp.cosh(t) / (mp.cosh(sh) ** 2) * step
        if mp.mpf('1e-100') < x < 1 - mp.mpf('1e-100'):
            nodes.append((x, omx, w))
    return nodes


NODES = make_nodes(mp.mpf('0.125'), 60)


def coeff(t, b, j):
    """h_b(t+j) = Gamma(t+b+j)/(Gamma(b) Gamma(t+j+1)) — the source Eq.(1) coefficient."""
    return mp.gamma(t + b + j) / (mp.gamma(b) * mp.gamma(t + j + 1))


def psi_direct(a, b, al, be, n):
    """Literal Conjecture 2 coefficient via Gamma products: no k! weighting."""
    return sum(coeff(a + al, b, k) * coeff(a + be, b, n - k)
               - coeff(a, b, k) * coeff(a + al + be, b, n - k)
               for k in range(n + 1))


def Sn_via_H(p, q, b, n):
    """Public registry route: S_n = mixtureFactor * betaMean(H_{c,n,b}; (p+q)/2,(p-q)/2).

    F_s(v) = int_0^1 w_b(s*v+(1-s)*u) du = (1/(1-s)) int_{s v}^{s v+1-s} w_b(t) dt,
    H(c,n,b)(v) = B(c,n+2)^-1 int_0^1 s^(c-1)(1-s)^(n+1) F_s(v) ds,
    betaMean(d) = int_0^1 v^(c/2+d-1)(1-v)^(c/2-d-1) H(v) dv / B(c/2+d, c/2-d).
    """
    c, bf = p + q, b

    def F(s, v):
        # int_{sv}^{sv+1-s} (t(1-t))^(b-1) dt, computed directly by betainc
        # (no cancellation even when the interval is exponentially small).
        return mp.betainc(bf, bf, s * v, s * v + 1 - s, regularized=False) / (1 - s)

    def H(v):
        norm = mp.beta(c, n + 2)
        acc = mp.mpf(0)
        for s, oms, ws in NODES:
            acc += ws * s ** (c - 1) * oms ** (n + 1) * F(s, v)
        return acc / norm

    def beta_mean(d):
        p_, q_ = c / 2 + d, c / 2 - d
        acc = sum(v ** (p_ - 1) * omv ** (q_ - 1) * H(v) * wv
                  for v, omv, wv in NODES)
        return acc / mp.beta(p_, q_)

    return (n + 1) * mp.gamma(c + n + 2 * bf) / (mp.gamma(bf) ** 2 * mp.gamma(c + n + 2)) \
        * beta_mean((p - q) / 2)


def psi_via_H(a, b, al, be, n):
    return Sn_via_H(a + al, a + be, b, n) - Sn_via_H(a, a + al + be, b, n)


cases = [(3, '0.7', '1.3', '2.7', 5),
         (2.5, '2', '0.3', '4', 4),
         (2.5, '2', '4', '0.3', 4),
         (0.3, '5', '1', '1', 4),
         (0.5, '0.3', '0.2', '0.9', 3),
         (7.3, '0.2', '0.1', '0.1', 1),
         (3, '0.1', '0.5', '2', 3),
         (4.2, '0.3', '0.7', '0.7', 2)]

checks = []
for (b, a, al, be, n) in cases:
    L = psi_direct(mp.mpf(a), mp.mpf(str(b)), mp.mpf(al), mp.mpf(be), n)
    R = psi_via_H(mp.mpf(a), mp.mpf(str(b)), mp.mpf(al), mp.mpf(be), n)
    rel = abs(L - R) / abs(L)
    checks.append({'b': str(b), 'a': a, 'alpha': al, 'beta': be, 'n': n,
                   'psi_direct': mp.nstr(L, 30), 'psi_via_H': mp.nstr(R, 30),
                   'rel_diff': mp.nstr(rel, 10),
                   'sign_matches_conjecture': (L > 0) if b > 1 else (L < 0)})

out = {
    'purpose': ('Independent numerical cross-check of the public resolution route for Karp '
                '1509.05120v1 Conjecture 2 (direct Gamma-product psi vs the shifted-beta '
                'mixture / H-kernel / beta-mean route). Consistency evidence only; the '
                'proof is the public Lean development at trureturing commit 337295b.'),
    'method': (f'psi_direct: mpmath gamma products at 30 dps; route side: tanh-sinh '
               f'quadrature, {len(NODES)} nodes per integral (step 0.125, x in '
               '[1e-100, 1-1e-100]); parameters with a beta shape below 0.1 excluded '
               '(mean concentrates below reachable quadrature depth)'),
    'memory_cap_mib': 512,
    'checks': checks,
    'all_route_identities_agree': all(float(c['rel_diff']) < 1e-7 for c in checks),
    'all_signs_match_conjecture': all(c['sign_matches_conjecture'] for c in checks),
    'is_proof': False,
}
Path(__file__).with_name('verify_route_chain.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({'max_rel_diff': max(float(c['rel_diff']) for c in checks),
                  'all_signs_match_conjecture': out['all_signs_match_conjecture']}))
