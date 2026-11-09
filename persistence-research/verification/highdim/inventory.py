import sys
sys.dont_write_bytecode = True
import os, json, collections, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import run_target

def enum_module(small=False):
    path = os.path.join(ROOT, 'verification', 'indep3' if small else 'indep2',
                        'i3_enum.py' if small else 'e_enum.py')
    spec = importlib.util.spec_from_file_location('enumeration', path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def configurations(t):
    small = t in (16, 24, 32)
    E = enum_module(small)
    allc = E.configs(t)
    cfg = [(S, far, v) for (S, far), v in allc.items()
           if len(far) >= 3 and not v['dead_weak' if small else 'dead40']]
    return sorted(cfg)

if __name__ == '__main__':
    for t in (112, 16, 24, 32, 111132, 14112):
        fn = os.path.join(HERE, f'results_t{t}.json')
        res = json.load(open(fn)) if os.path.exists(fn) else {}
        cfg = configurations(t)
        print(t, 'authoritative', len(cfg), 'status', dict(collections.Counter(
            r['status'] for r in res.values())), 'far dims', dict(collections.Counter(len(f)+1 for _, f, _ in cfg)))
        if t == 112:
            for S, f, v in cfg:
                r = res.get(f"{S}|{','.join(map(str, f))}", {})
                print(' ', S, list(f), r.get('status'), r.get('slices'), r.get('certs'),
                      sum(j.get('info', {}).get('nodes', 0) for j in r.get('jobs', [])))
        if t in (16, 24, 32):
            for S, f, v in cfg:
                sl = run_target.slices(9*S-1, f)
                print(' ', S, list(f), 'slices', len(sl), 'maxdim', max(len(g)+1 for _, g in sl))
