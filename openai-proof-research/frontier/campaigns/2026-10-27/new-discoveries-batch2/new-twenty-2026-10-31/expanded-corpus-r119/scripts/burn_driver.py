"""Resumable driver for burn2: python3 -I burn_driver.py n L chunk max_calls
State in outputs/burn/n{n}-L{L}/state.json; D(m) lists in D{m}.bin; each chunk runs under scripts/limited.py
(2 CPUs, CPU 120 s, wall 140 s, RSS 6 GiB) and its output is merged only after a clean return."""
import json, pathlib, subprocess, sys, re
D = pathlib.Path(__file__).resolve().parents[1]
n, L, chunk, maxcalls = map(int, sys.argv[1:5])
W = D / f'outputs/burn/n{n}-L{L}'; W.mkdir(parents=True, exist_ok=True)
sf = W / 'state.json'
st = json.loads(sf.read_text()) if sf.exists() else None
if st is None:
    m = 1
    while m * m < n * L: m += 1
    st = {'n': n, 'L': L, 'm': m, 'skip': 0, 'closed': False, 'levels': {}, 'nonib': [], 'calls': 0}
calls = 0
while not st['closed'] and calls < maxcalls:
    m = st['m']; prev = W / f'D{m-1}.bin'; cur = W / f'D{m}.bin'; tmp = W / 'chunk.bin'
    if tmp.exists(): tmp.unlink()
    name = f'burn2-n{n}-L{L}-m{m}-s{st["skip"]}'
    subprocess.run(['python3', '-I', str(D / 'scripts/limited.py'), name, str(D / 'scripts/burn2'), str(n), str(L), str(m),
                    str(prev) if prev.exists() else '-', str(tmp), str(st['skip']), str(chunk)], check=True, capture_output=True)
    rc = json.loads((D / f'logs/{name}.receipt.json').read_text())
    log = (D / f'logs/{name}.log').read_text()
    line = [l for l in log.splitlines() if l.startswith('n=')]
    if rc['returncode'] != 0 or rc['cap_reason'] or not line:
        print('chunk failed', name, rc); sys.exit(1)
    calls += 1; st['calls'] += 1
    s = line[-1]; g = lambda k: int(re.search(k + r'=(\d+)', s).group(1))
    with cur.open('ab') as f: f.write(tmp.read_bytes() if tmp.exists() else b'')
    lv = st['levels'].setdefault(str(m), {'ext_tested': 0, 'balanced_tested': 0, 'deficient': 0, 'IB': 0, 'nonIB': 0, 'cpu_wall_s': 0.0})
    lv['ext_tested'] += g('ext_tested'); a, b = map(int, re.search(r'bal_range=\[(\d+),(\d+)\)', s).groups()); lv['balanced_tested'] += b - a
    lv['deficient'] += g('deficient'); lv['IB'] += g(' IB'); lv['nonIB'] += g('nonIB'); lv['cpu_wall_s'] += rc['wall_seconds']
    st['nonib'] += [l for l in log.splitlines() if l.startswith('NONIB')]
    if s.endswith('DONE'):
        if not cur.exists(): cur.write_bytes(b'')
        U1 = 2 * (m + 1) - 2 + L
        if lv['deficient'] == 0 and n * U1 < (m + 1) ** 2: st['closed'] = True
        st['m'] = m + 1; st['skip'] = 0
    else:
        st['skip'] = b
    sf.write_text(json.dumps(st, indent=1) + '\n')
print(json.dumps({k: st[k] for k in ('m', 'skip', 'closed', 'calls')}), 'nonIB', len(st['nonib']), st['nonib'][:5])
print({m: (v['deficient'], v['nonIB']) for m, v in st['levels'].items()})
