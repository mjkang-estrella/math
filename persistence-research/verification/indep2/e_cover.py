# Agent E: coverage audit.  Compares my enumeration (e_enum.py) to C's solve_t*.json and certificate metas.
import json, glob, os, collections, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e_enum import *
C = '../glm/L2c/'
certs = {}   # file -> meta
for f in sorted(glob.glob(C + 'cert_t*.jsonl')):
    with open(f) as fh: m = json.loads(fh.readline())
    certs[os.path.basename(f)] = m
bykey = collections.defaultdict(list)
for f, m in certs.items(): bykey[(m['K'], tuple(m['coefs']))].append((f, m))
report = {}
for T in TARGETS:
    mine = configs(T)
    sj = json.load(open(C + f'solve_t{T}.json'))
    theirs = {}
    for ms in sj['multisets']:
        for cf in ms['configs']:
            key = (cf['S_low'], tuple(cf['far']))
            assert key not in theirs, key
            theirs[key] = dict(cf, multiset=tuple(ms['multiset']))
    R = dict(T=T, total=len(mine))
    R['only_mine'] = sorted(set(mine) - set(theirs)); R['only_theirs'] = sorted(set(theirs) - set(mine))
    # multiset agreement
    R['multiset_mismatch'] = [k for k in mine if k in theirs and tuple(mine[k]['multiset']) != theirs[k]['multiset']]
    # parity
    R['their_dead_but_mine_alive'] = [k for k in theirs if theirs[k]['status'] == 'parity-dead' and k in mine and not mine[k]['dead40']]
    R['mine_dead_not_labelled_dead'] = [(k, theirs[k]['status']) for k in mine if mine[k]['dead40'] and k in theirs and theirs[k]['status'] != 'parity-dead']
    R['dead'] = sum(1 for k in mine if mine[k]['dead40'])
    # alive configs
    alive = [k for k in mine if not mine[k]['dead40']]
    R['alive'] = len(alive)
    cat = collections.Counter(); uncovered = []; detail = []
    certs_used = set(); cert_mismatch = []
    for k in alive:
        S_low, farA = k
        nfar = len(farA)
        st = theirs.get(k, {}).get('status', 'MISSING')
        if nfar >= 3:
            if st.startswith('OPEN'): cat['open(>=3 far)'] += 1
            else: cat['UNCOVERED(>=3 far, status=%s)' % st] += 1; uncovered.append((k, st))
            continue
        K0 = 9 * S_low - 1
        sl = slices(K0, farA)
        need = []   # (K', coefs perm, qmin)
        for (Kp, F, qmin, fixed) in sl:
            for pm in (perms(F) if F else [()]):
                need.append((Kp, pm, qmin, fixed))
        ok = True; miss = []
        for (Kp, pm, qmin, fixed) in need:
            cands = bykey.get((Kp, tuple(pm)), [])
            good = [(f, m) for f, m in cands if m['qmin'] <= qmin and m['qmin'] > v2(Kp) and m['dim'] == len(pm) + 1 and m['root']['m'] == 1 and m['target'] == T]
            if not good:
                ok = False; miss.append((Kp, pm, qmin, fixed, [(f, m['qmin'], m['root']['m'], m['target']) for f, m in cands]))
            else:
                for f, m in good: certs_used.add(f)
        if ok: cat['certified(<=2 far)'] += 1
        else:
            if st.startswith('OPEN'): cat['open(<=2 far, declared)'] += 1
            else: cat['UNCOVERED(<=2 far, status=%s)' % st] += 1; uncovered.append((k, st, miss[:3]))
        detail.append((k, st, ok, len(need)))
        # compare C's claim with mine
        if (st == 'PROVED') != ok: cert_mismatch.append((k, st, ok, miss[:2]))
    R['categories'] = dict(cat); R['uncovered'] = uncovered; R['cert_mismatch'] = cert_mismatch
    R['certs_used'] = len(certs_used)
    allt = {f for f, m in certs.items() if m['target'] == T}
    R['certs_unused'] = sorted(allt - certs_used)
    R['their_status'] = dict(collections.Counter(v['status'].split(' (')[0] for v in theirs.values()))
    R['their_proved_with_ge3far'] = [k for k, v in theirs.items() if v['status'] == 'PROVED' and len(k[1]) >= 3]
    R['nslice_total'] = sum(d[3] for d in detail)
    report[T] = R
    print('=== target', T)
    for kk, vv in R.items():
        if kk in ('uncovered', 'cert_mismatch', 'certs_unused'): print('  ', kk, len(vv), vv[:6])
        else: print('  ', kk, vv if not isinstance(vv, list) else (len(vv), vv[:5]))
json.dump(report, open('e_cover_out.json', 'w'), default=str, indent=1)
