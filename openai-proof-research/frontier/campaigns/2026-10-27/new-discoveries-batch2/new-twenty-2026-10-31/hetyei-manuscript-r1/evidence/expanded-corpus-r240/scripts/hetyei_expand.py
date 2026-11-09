"""Print hand-checkable expansions: I2(aab) term by term, and I2 of each word of the n=5 certificate
(number of terms). Uses the certificate implementation (ER Definition 9.1).  Usage: hetyei_expand.py SCRIPTDIR"""
import sys
SD = sys.argv[-1]
src = open(SD + '/hetyei_certificates.py').read(); cut = src.index('res = {}')
ns = {}; exec(compile(src[:cut], 'cert_head', 'exec'), ns)
M, I2w, cop = ns['M'], ns['I2w'], ns['cop']
for w in ['aab', 'baa']:
    print('I2(%s) = %s + %s' % (w, w, w[::-1]), end='')
    for u1, u2 in cop(w):
        print(' + M(%r,%r)=%s' % (u1[::-1], u2, dict(sorted(M(u1[::-1], u2).items()))), end='')
    print('\n   total:', dict(sorted(I2w(w).items())))
u = {'aaaba': 1, 'aaabb': 1, 'aabaa': -2, 'aabba': -1, 'aabbb': 1, 'abaaa': 1, 'abaab': 1, 'abbaa': -1,
     'abbab': 1, 'abbba': -2, 'baaab': -2, 'baaba': 1, 'baabb': -1, 'babba': 1, 'babbb': 1, 'bbaaa': 1,
     'bbaab': -1, 'bbabb': -2, 'bbbaa': 1, 'bbbab': 1}
tot = 0
for w in sorted(u):
    img = I2w(w); tot += sum(abs(c) for c in img.values())
    print(w, u[w], 'I2 terms', len(img), 'abs coeff sum', sum(abs(c) for c in img.values()))
print('total absolute coefficient mass of the expansion', tot)
# the reduced form: u = v + v* with v supported on 10 words (one per reversal orbit)
reps = sorted({min(w, w[::-1]) for w in u})
print('orbit representatives', len(reps), {r: u[r] for r in reps})
