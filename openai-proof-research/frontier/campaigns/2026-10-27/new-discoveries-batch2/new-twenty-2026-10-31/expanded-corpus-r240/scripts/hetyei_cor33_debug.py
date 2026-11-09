"""Locate Corollary 33 discrepancies between the two implementations (certificates vs literal_vbu).
Usage: hetyei_cor33_debug.py NMAX SCRIPTDIR"""
import sys, importlib.util, itertools
SD = sys.argv[-1]; NMAX = int(sys.argv[1])
def load(name, path, argv):
    old = sys.argv; sys.argv = argv
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec)
    try: spec.loader.exec_module(m)
    finally: sys.argv = old
    return m
lv = load('lv', SD + '/hetyei_literal_vbu.py', ['x', SD])
src = open(SD + '/hetyei_certificates.py').read()
cut = src.index('res = {}')
ns = {}; exec(compile(src[:cut], 'cert_head', 'exec'), ns)
bad = 0
for n in range(1, NMAX + 1):
    for w in (''.join(t) for t in itertools.product('ab', repeat=n)):
        a = ns['I2w'](w); b = lv.I2word(w)
        if a != b:
            bad += 1
            if bad <= 4: print('I2 differs', w, a, b)
        if n <= NMAX:
            d = ns['I2']({w: 1, w[::-1]: -1})
            if d and bad < 10: print('Cor33 fails (cert impl) for', w, d); bad += 1
print('done; issues', bad)
