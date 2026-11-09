# r7 p2_finish.py — iterate wide-kill + deepen on the 3-D residual classes until
# closed (or a hard core remains). Reuses p2_twofar machinery.
# Run: bash -c 'ulimit -v 3000000; python3 -I p2_finish.py'

import json, math, os, sys, importlib.util
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("p2t", os.path.join(here, "p2_twofar.py"))
T = importlib.util.module_from_spec(spec); T.__name__ = "p2t"
spec.loader.exec_module(T)
spec2 = importlib.util.spec_from_file_location("p2r", os.path.join(here, "p2_resid.py"))
R = importlib.util.module_from_spec(spec2); R.__name__ = "p2r"
spec2.loader.exec_module(R)

MAXM = int(os.environ.get('P2MAXM2', '50000000000'))
CLASS_CAP = 2_000_000

def resume(K, t0, qlo, residual, brute, maxm):
    bruteS = set(brute)
    stack = [tuple(x) for x in residual]
    seen = set(); nc = 0; reasons = {}; recorded = []; residual2 = []
    def check_no_sol(key, tag):
        rhoL, rho1, rho2, M, _ph = key
        for (L, q1, q2) in bruteS:
            if q1 >= qlo and L % M == rhoL % M and q1 % M == rho1 % M and q2 % M == rho2 % M:
                raise AssertionError(f"FALSE KILL [{tag}] {key} contains {(L,q1,q2)}")
    while stack:
        key = stack.pop()
        if key in seen: continue
        seen.add(key)
        nc += 1
        if nc % 100000 == 0:
            print(f"   ..nc={nc} stack={len(stack)} Mmax={key[3]}", flush=True)
        if nc > CLASS_CAP:
            return dict(status="CAP", nc=nc, recorded=recorded, residual=stack + residual2)
        rhoL, rho1, rho2, M, ph = key
        sig = T.signature3(K, rhoL, rho1, rho2, M)
        (a_lo, a_hi), (w_lo, w_hi) = sig
        if a_hi is not None and w_hi is not None:
            rec = T.size_solutions3(K, t0, rhoL, rho1, rho2, M, a_lo, w_lo, qlo)
            for s in rec:
                assert s in bruteS, f"recorded {s} not in brute list"
            recorded += rec
            reasons["size"] = reasons.get("size", 0) + 1
            continue
        kill = R.wide_try_kill(K, t0, qlo, rhoL, rho1, rho2, M, sig)
        if kill:
            check_no_sol(key, kill[0])
            reasons[kill[0]] = reasons.get(kill[0], 0) + 1
            continue
        ua = a_hi is None; uw = w_hi is None
        if ua and not uw: mult = 3
        elif uw and not ua: mult = 7
        else: mult = 3 if ph % 2 == 0 else 7
        which = ph % 3
        nM = M * mult
        if nM > maxm:
            residual2.append(key); continue
        rs = [rhoL, rho1, rho2]
        for s in range(mult):
            nr = list(rs)
            nr[which] = (nr[which] + s * M) % nM
            stack.append((nr[0], nr[1], nr[2], nM, ph + 1))
    return dict(status="CLOSED", nc=nc, recorded=sorted(set(recorded)), reasons=reasons,
                residual=residual2)

for S in (10, 1):
    residual = json.load(open(os.path.join(here, f"residual_3d_S{S}.json")))
    qlo = 4 if S == 1 else 3
    t0 = T.vp(9 * S - 1, 2)
    brute = T.brute_twofar(S, T.LCHECK)
    rnd = 0
    while residual and rnd < 6:
        rnd += 1
        print(f"S={S} round {rnd}: {len(residual)} residual classes", flush=True)
        res = resume(9 * S - 1, t0, qlo, residual, brute, MAXM)
        print(f"  -> {res['status']} nc={res['nc']} recorded={res['recorded']} "
              f"reasons={res['reasons']} residual={len(res['residual'])}", flush=True)
        residual = res['residual']
        if res['status'] == 'CAP':
            json.dump(residual, open(os.path.join(here, f"residual2_3d_S{S}.json"), "w"))
            break
    if not residual:
        print(f"S_low={S} two-far 3-D: FULLY CLOSED", flush=True)
    else:
        json.dump(residual, open(os.path.join(here, f"residual2_3d_S{S}.json"), "w"))
