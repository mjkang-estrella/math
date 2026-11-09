# Structural validity of the metadata of ALL sym2 certificates (from kill_usage.json): the conditions under which pin2 / tail pin / V2 are sound.
import json, collections, glob, os
k = json.load(open('../highdim/sym2/kill_usage.json'))
def v2(n):
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c
bad = collections.Counter(); n = 0; ex = []
stat = collections.Counter()
for f, v in k.items():
    m = v['meta']
    if m['scope'] != 'full': stat['scope!=full (controls, not used for closure)'] += 1; continue
    n += 1
    t0 = v2(m['K']); q = m['qmin']; kk = m.get('pin_digits') or 0; p2 = bool(m.get('pin2'))
    ok = True
    def chk(c, name):
        global ok
        if not c: bad[name] += 1; ok = False; ex.append((f, name))
    chk(m['K'] > 0 and m['K'] % 5 != 0, 'K>0 and 5 does not divide K')
    chk(q > t0, 'qmin>v2(K)')
    chk((not p2) or q >= t0 + 3, 'pin2 => qmin>=t0+3')
    chk(0 <= kk <= min(3, q), 'pin_digits<=min(3,qmin)')
    chk(m['domain'] == 'unordered' and m['format'] == 'nd-sym' and m['version'] == 1, 'format')
    chk(m['root']['m'] == 1 and m['root']['r'][0] == 0 and all(not any(g) for g in m['root']['r'][1:]), 'root all-zero mod 1')
    chk(m['dim'] == 1 + sum(g[1] for g in m['groups']), 'dim')
    chk(len({g[0] for g in m['groups']}) == len(m['groups']), 'distinct coefficients')
    stat[('pin2', p2)] += 1; stat[('tail k', kk)] += 1; stat[('t0>=k and tail', t0 >= kk and kk > 0)] += 1; stat[('qmin>t0+3 and pin2', q > t0 + 3 and p2)] += 1
print('full-scope certificates examined:', n, '| violations:', dict(bad), '| examples:', ex[:3])
print(dict(stat))
