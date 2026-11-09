"""Referee's independent re-implementation of the hypotheses of Lemmas lem:propP, lem:propL,
lem:F1 and Proposition prop:certM, from the paper's text only.  Data from spider3 (own C++ solver).
Usage: mycert.py x y Z      (Z = range of r on which the closed forms are fitted/validated)
Reports the minimal R_1 the lemmas need, z1, z0."""
import sys, subprocess, resource
sys.setrecursionlimit(1 << 20)
from spider import Gamma, rho, times

x, y, Z = map(int, sys.argv[1:4])
resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
out = subprocess.run(['nice', './spider3', str(x), str(y), str(Z), 'dump'], capture_output=True, text=True, check=True).stdout
S, P = 'nio', 'FIO'
fam = {}
gfree = None
for line in out.splitlines():
    t = line.split()
    if t[0] == 'G':
        gfree = [None] + list(map(int, t[1:]))
        continue
    s, a, b, phi = map(int, t[1:5])
    K = tuple(sorted([(c // 3, P[c % 3]) for c in (a, b) if c // 3 > 0]))
    v = [None] + list(map(int, t[5:]))
    key = (S[s], K, P[phi])
    if key in fam:
        assert fam[key] == v
    fam[key] = v


def short_moves(s, K):
    """yield (d, kind, succ, delta)"""
    for idx, (h, psi) in enumerate(K):
        rest = K[:idx] + K[idx + 1:]
        for j in range(1, h + 1):
            for dl in 'IO':
                if j == h and psi != 'F' and dl != psi:
                    continue
                d = rho(h - j, dl, psi)
                if j >= 2:
                    yield d, 'a1', (s, tuple(sorted(rest + ((j - 1, dl),)))), dl
                elif s == 'n':
                    yield d, 'a1', (times(s, dl), rest), dl
                elif times(s, dl) == 'f':
                    yield d, 'a2', None, dl
                else:
                    yield d, 'a3', None, dl


k0 = ('n', tuple(sorted(((x, 'F'), (y, 'F')))))
confs, st = {k0}, [k0]
while st:
    k = st.pop()
    for d, kind, sc, _ in short_moves(*k):
        if kind == 'a1' and sc not in confs:
            confs.add(sc); st.append(sc)
confs = sorted(confs)

# --- fit arithmetic-periodic forms, demanding validity on a long tail [r0, Z]
form = {}
for k in confs:
    for phi in 'IO':
        v = fam[(k[0], k[1], phi)]
        got = None
        for p in (1, 2, 4, 8, 16, 32, 64):
            for e in (0, 1):
                r0 = Z - p
                while r0 >= 1 and v[r0 + p] == v[r0] + e * p:
                    r0 -= 1
                r0 += 1
                if r0 <= Z - 4 * p - 100:
                    got = (p, e, r0); break
            if got: break
        assert got, ('no form', k, phi)
        form[(k, phi)] = got
PI = max([2] + [f[0] for f in form.values()])
typ, q, r0 = {}, {}, {}
for k in confs:
    es = {form[(k, phi)][1] for phi in 'IO'}
    assert len(es) == 1, ('mixed type', k)
    typ[k] = 'L' if es.pop() else 'P'
    for phi in 'IO':
        p, e, rr = form[(k, phi)]
        r0[(k, phi)] = rr
        v = fam[(k[0], k[1], phi)]
        q[(k, phi)] = [None] * PI
        for res in range(PI):
            r = rr + (res - rr) % PI
            q[(k, phi)][res] = v[r] - e * r
        for r in range(rr, Z + 1):       # validate form on [r0, Z]
            assert v[r] == e * r + q[(k, phi)][r % PI]


def cf(k, phi, r):
    if r < r0[(k, phi)]:
        return fam[(k[0], k[1], phi)][r]
    return (r if typ[k] == 'L' else 0) + q[(k, phi)][r % PI]


rhat = max(r0.values())
MP = max(max(fam[(k[0], k[1], phi)][1:]) for k in confs for phi in 'IO' if typ[k] == 'P')
D = max(d for k in confs for d, *_ in short_moves(*k))
lam = min([0] + [min(q[(k, phi)]) for k in confs for phi in 'IO' if typ[k] == 'L'])
Q = PI
while Q <= D:
    Q *= 2
RP = max(2 * PI + 1 + rhat, PI + MP + D - lam + 1)
nL = sum(typ[k] == 'L' for k in confs)
print('(%d,%d): |K|=%d, Pi=%d, typeL=%d, rhat=%d, M_P=%d, D=%d, lambda=%d, Q=%d, R_P=%d'
      % (x, y, len(confs), PI, nL, rhat, MP, D, lam, Q, RP))

W = {k: {dl: Gamma(times(k[0], dl), k[1]) for dl in 'IO'} for k in confs}
ok = True
need_R1 = RP
for k in confs:
    if typ[k] != 'L':
        continue
    rk = max(r0[(k, 'I')], r0[(k, 'O')])
    E = {}
    for phi in 'IO':
        for vr in (0, 1):
            for io in range(PI):
                for dl in 'IO':
                    qq = q[(k, dl)][io]
                    b = ((vr - 1 - io) % 2) ^ (dl != phi)
                    E[(phi, vr, io, dl)] = qq + b - 2 * b * ((io + qq) % 2)
            if len({(io + E[(phi, vr, io, dl)]) % PI for io in range(PI) for dl in 'IO'}) != PI:
                ok = False; print('W1 fails', k, phi, vr)
    em, eM = min(E.values()), max(E.values())
    qp = max(max(q[(k, dl)]) for dl in 'IO')
    ell, Kc = rk + eM, 2 - em
    M = qp + Kc + 1
    amax = max([fam[(k[0], k[1], dl)][i] for dl in 'IO' for i in range(1, rk)] + [0])

    def small_opts(R, phi, imax):
        Sx = set()
        for d, kind, sc, dl in short_moves(*k):
            if kind == 'a1' and typ[sc] == 'P':
                Sx.add(d ^ cf(sc, phi, R))
            elif kind == 'a3':
                Sx.add(d ^ rho(R, 'O' if k[0] == 'i' else 'I', phi))
        for dl in 'IO':
            Sx.add(rho(R - 1, dl, phi) ^ W[k][dl])
        nos = set(Sx)
        for i in range(1, imax + 1):
            for dl in 'IO':
                Sx.add(cf(k, dl, i) ^ rho(R - 1 - i, dl, phi))
        return nos, Sx

    base = rhat + 2 + PI
    smax = max(max(small_opts(R, phi, 0)[0]) for R in range(base, base + PI) for phi in 'IO')
    # smallest i_max >= r_kappa for which (W2) holds
    found = None
    for imax in range(rk, rk + 200):
        RW = max(rk + M, smax + Kc + 1, amax + Kc + 2, imax + 2, rhat + PI + 1)
        if all(set(range(ell)) <= small_opts(R, phi, imax)[1] for R in range(RW, RW + PI) for phi in 'IO'):
            found = (imax, RW); break
    if not found:
        ok = False; print('W2 fails for', k); continue
    need_R1 = max(need_R1, found[1] + Q)

# --- Prop certM
c_set = set(q[(k0, 'I')] + q[(k0, 'O')])
rk0 = max(r0[(k0, 'I')], r0[(k0, 'O')])
assert typ[k0] == 'L' and len(c_set) == 1
c = c_set.pop()
assert c % 2 == 0
assert fam[(k0[0], k0[1], 'I')][1:rk0] == fam[(k0[0], k0[1], 'O')][1:rk0]
z1 = max([2 * rk0 + c + 1, max(W[k0].values()) + 3] + [i + fam[(k0[0], k0[1], 'I')][i] + 3 for i in range(1, rk0)])
nM1 = nM2 = 0
for d, kind, sg, _ in short_moves(*k0):
    if sg in (('i', ((1, 'F'),)), ('o', ((1, 'F'),))) and d >= 2 and \
            all((cf(sg, dl, i) - i) % 2 == 1 for dl in 'IO' for i in range(1, Z + 1)) and typ[sg] == 'L' and \
            all(qq % 2 == 1 for dl in 'IO' for qq in q[(sg, dl)]):
        nM1 += 1
        continue
    if typ[sg] != 'P':
        ok = False; print('certM: successor neither M1 nor P', sg); continue
    nM2 += 1
    for p in range(PI):
        for v in range((d | 1) + 1):
            best = None
            for t in range(0, 300):
                for dl in 'IO':
                    if t ^ q[(sg, dl)][(p - 1 - t) % PI] == v:
                        cand = t + 1 + r0[(sg, dl)]
                        best = cand if best is None else min(best, cand)
            if best is None:
                ok = False; print('M2 fails', sg, p, v)
            else:
                z1 = max(z1, best)
viol = [z for z in range(1, Z + 1) if gfree[z] != z % 2]
z0 = max(viol) + 1 if viol else 1
print('(%d,%d): hypotheses %s; minimal R_1 needed = %d; kappa0: c=%d r=%d W=%s; M1=%d M2=%d short moves; z1=%d; z0=%d (direct, z<=%d)'
      % (x, y, 'OK' if ok else 'FAIL', need_R1, c, rk0, W[k0], nM1, nM2, z1, z0, Z))
