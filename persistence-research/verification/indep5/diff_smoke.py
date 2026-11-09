import sys, os, random
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_sym_F5 as F5
import check_sym_F_base as B

def mk(mod, kt):
    c = mod.Cert.__new__(mod.Cert)
    c.kt = kt
    c._pairs = {}
    if mod is F5: c._ps = {}; c._admc = {}
    return c

def allowed_old(kt, E, sg, p):
    c = mk(B, kt)
    A, W, P = B.Cert.pairs(c, E)
    a0, aex, w0, wex = sg
    h = []
    if not aex: h.append(pow(3, A, p))
    if not wex: h.append(pow(7, W, p))
    nH = 1
    for x in h: nH = B.lcm(nH, B.order(x, p))
    img = set()
    for al, be in P:
        if aex and (al - a0) % A: continue
        if wex and (be - w0) % W: continue
        ae = a0 if aex else al
        be_ = w0 if wex else be
        img.add(pow(pow(3, ae, p) * pow(7, be_, p) % p, nH, p))
    return {y for y in range(1, p) if pow(y, nH, p) in img}

def allowed_new(kt, E, sg, p):
    c = mk(F5, kt)
    rep, nU = F5.Cert._adm(c, p, E, sg)
    if rep is None: return None
    return {y for y in range(1, p) if pow(y, nU, p) == pow(rep, nU, p)}

random.seed(1)
cases = bad = 0
for trial in range(300):
    e2 = random.randint(0, 5); e5 = random.randint(0, 4)
    E = 2**e2 * 5**e5
    if E > 50000: continue
    kt = random.randrange(1, 10**6, 2)   # odd
    if e5 and random.random() < 0.15: kt = kt * 5  # sometimes 5 | K0
    for aex in (0, 1):
        for wex in (0, 1):
            a0 = random.randrange(0, 12); w0 = random.randrange(0, 12)
            sg = (a0, aex, w0, wex)
            for p in (11, 13, 41, 73):
                o = allowed_old(kt, E, sg, p) or set()
                n = allowed_new(kt, E, sg, p)
                if n is None: n = set()
                cases += 1
                if o != n:
                    bad += 1
                    if bad < 5: print("MISMATCH", E, kt, sg, p, len(o) if o else None, len(n) if n else None)
print("cases", cases, "bad", bad)
