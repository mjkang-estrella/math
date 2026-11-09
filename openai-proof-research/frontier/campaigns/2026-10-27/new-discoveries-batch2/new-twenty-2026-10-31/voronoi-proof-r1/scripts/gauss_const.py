# Gaussian constants: h_o = int phi^3 Phi^5, h_d = -int g phi^2 Phi^6 (check h_d = -3 h_o), and the
# predicted Gaussian corner slope of 8*Gamma per moved coordinate: -6 h_o / t.
import math
def phi(x): return math.exp(-x * x / 2) / math.sqrt(2 * math.pi)
def Phi(x): return 0.5 * math.erfc(-x / math.sqrt(2))
def integ(fn, a=-12, b=12, N=200000):
    h = (b - a) / N; s = fn(a) + fn(b)
    for i in range(1, N): s += (4 if i % 2 else 2) * fn(a + i * h)
    return s * h / 3
ho = integ(lambda g: phi(g) ** 3 * Phi(g) ** 5)
hd = -integ(lambda g: g * phi(g) ** 2 * Phi(g) ** 6)
p8 = integ(lambda g: phi(g) * Phi(g) ** 7)
print('h_o =', ho, ' h_d =', hd, ' h_d/h_o =', hd / ho, ' check P(G0 max of 8) =', p8)
print('Gaussian slope of 8*Gamma per moved coordinate: -6 h_o / t = -%.6f / t' % (6 * ho))
