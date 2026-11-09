"""Stable density f_alpha (positive alpha-stable, Laplace e^{-lam^alpha}) via Zolotarev's
convergent tail series, valid for 0<alpha<1 and all x>0:

  f_alpha(x) = (1/pi) * sum_{k>=1} (-1)^{k+1} Gamma(1+alpha k) sin(pi alpha k)/k! * x^{-alpha k - 1}

Plus the log-convolution identity of Simon 1412.0132 sec 2.2:

  K_alpha(e^{alpha x}, e^{alpha y})
      = pi e^{(1-alpha)(x+y)} / sin(pi alpha) * int_R f_alpha(e^{x-u}) f_alpha(e^{y-u}) e^{-2u} du
"""
import mpmath as mp


def falpha(x, alpha, terms=None):
    """Density of positive alpha-stable law at x>0, 0<alpha<1, via convergent series."""
    x = mp.mpf(x)
    alpha = mp.mpf(alpha)
    s = mp.mpf(0)
    k = 1
    small_run = 0
    while True:
        term = (-1) ** (k + 1) * mp.gamma(1 + alpha * k) * mp.sin(mp.pi * alpha * k) / mp.factorial(k) * x ** (-alpha * k - 1)
        s += term / mp.pi
        # terms may vanish exactly (sin(pi*alpha*k)=0); require 3 consecutive tiny terms
        if terms is not None and k >= terms:
            break
        if abs(term) < mp.mpf(10) ** (-mp.mp.dps - 8) * abs(s) or k > 20000:
            small_run += 1
            if small_run >= 3:
                break
        else:
            small_run = 0
        k += 1
    return s


def falpha_half(x):
    """Closed form for alpha=1/2: (1/(2*sqrt(pi))) x^{-3/2} exp(-1/(4x))."""
    x = mp.mpf(x)
    return 1 / (2 * mp.sqrt(mp.pi)) * x ** (-mp.mpf(3) / 2) * mp.e ** (-1 / (4 * x))


def K(a, t, x):
    """Cauchy kernel 1/(t^2 + 2 cos(pi a) t x + x^2)."""
    t = mp.mpf(t); x = mp.mpf(x); a = mp.mpf(a)
    return 1 / (t ** 2 + 2 * mp.cos(mp.pi * a) * t * x + x ** 2)


def logconv(x, y, alpha, tol=mp.mpf('1e-30')):
    """int_R f_alpha(e^{x-u}) f_alpha(e^{y-u}) e^{-2u} du by adaptive quadrature."""
    x = mp.mpf(x); y = mp.mpf(y)
    h = lambda u: falpha(mp.e ** (x - u), alpha) * falpha(mp.e ** (y - u), alpha) * mp.e ** (-2 * u)
    # integrand decays like e^{-2u} e^{-(alpha+1)(x-u)} for u->-inf ~ e^{alpha u}; and for u->+inf like e^{-2u} f(e^{x-u}) with e^{x-u}->0 tail f(z) ~ z^{-alpha-1}: e^{-2u} e^{-(alpha+1)(u-x)} -> super small. So [-60, 60] amply suffices; use mp.quad with split.
    return mp.quad(h, [-80, -20, -5, 0, 5, 20, 80])


def rep_check(x, y, alpha):
    lhs = K(alpha, mp.e ** (alpha * x), mp.e ** (alpha * y))
    rhs = mp.pi * mp.e ** ((1 - alpha) * (x + y)) / mp.sin(mp.pi * alpha) * logconv(x, y, alpha)
    return lhs, rhs
