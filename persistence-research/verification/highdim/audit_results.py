"""Reconcile every E/E2 configuration; independently replay E/E2 slice covers.
Usage: audit_results.py [--final]
Final mode requires a checker PASS with the current certificate hash, for both
checkers, for every generated certificate including partial configurations.
"""
import sys
sys.dont_write_bytecode = True
import os, json, glob, collections, itertools, functools, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from inventory import configurations, enum_module
from breadth import atomic_json

@functools.cache
def digest(fn):
    h = hashlib.sha256()
    with open(fn,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): h.update(b)
    return h.hexdigest()

def main():
    final = '--final' in sys.argv
    checksfn = os.path.join(HERE, 'checker_results.json')
    checks = json.load(open(checksfn)) if os.path.exists(checksfn) else {}
    problems = []; totals = {}; configs_out = {}
    all_files = sorted(glob.glob(os.path.join(HERE,'certs','**','*.jsonl'),recursive=True))
    meta = {}
    for fn in all_files:
        with open(fn) as f: meta[fn] = json.loads(next(f))
    verified = {}
    for fn in all_files:
        rel = os.path.relpath(fn,HERE)
        verified[fn] = all(checks.get(name+'|'+rel,{}).get('status') == 'PASS' and
                           checks.get(name+'|'+rel,{}).get('sha256') == digest(fn)
                           for name in ('hd','v14'))
    if final:
        for fn in all_files:
            if not verified[fn]: problems.append('not checked by both: '+os.path.relpath(fn,HERE))
    max_floor = 0
    for t in (16,24,32,112,111132,14112):
        cfg = configurations(t)
        resfn = os.path.join(HERE,f'results_t{t}.json')
        results = json.load(open(resfn)) if os.path.exists(resfn) else {}
        keys = {f"{S}|{','.join(map(str,far))}" for S,far,_ in cfg}
        if set(results) != keys:
            problems.append(f't={t}: missing={len(keys-set(results))} extra={len(set(results)-keys)}')
        E = enum_module(t in (16,24,32))
        # E/E2's independent, collision-aware recursive cover; it does not call
        # the resumed generator's slicing implementation.
        lookup = collections.defaultdict(list)
        for fn,m in meta.items():
            if os.path.dirname(fn) != os.path.join(HERE,'certs',f't{t}'): continue
            lookup[(m['K'],tuple(sorted(m['coefs'])))].append((fn,m))
        counts = collections.Counter(); cfgrecs = []
        for S,far,detail in cfg:
            key = f"{S}|{','.join(map(str,far))}"
            rec = results.get(key,{})
            status = rec.get('status','MISSING')
            cr = {'key':key,'multiset':list(detail['multiset']),'status':status,
                  'budget':rec.get('budget'), 'reason':rec.get('stop_reason'),
                  'slice_cover_ok':False, 'both_checkers':False}
            if status == 'CLOSED':
                need = E.slices(9*S-1,far)
                used = set(); holes = []
                for K,free,qmin,fixed in need:
                    max_floor = max(max_floor,qmin)
                    candidates = [(fn,m) for fn,m in lookup[(K,tuple(sorted(free)))] if m['qmin']<=qmin]
                    unordered = [(fn,m) for fn,m in candidates if m.get('domain','ordered')=='unordered']
                    if unordered:
                        used.add(unordered[0][0]); continue
                    for order in sorted(set(itertools.permutations(free))):
                        matching = [(fn,m) for fn,m in candidates if tuple(m['coefs'])==order]
                        if matching: used.add(matching[0][0])
                        else: holes.append([K,list(order),qmin,list(fixed)])
                cr.update(slice_cover_ok=not holes, both_checkers=all(verified[fn] for fn in used),
                          independent_slice_count=len(need), certificate_count=len(used),
                          holes=holes, files=sorted(os.path.relpath(fn,HERE) for fn in used))
                if holes: problems.append(f't={t} {key}: independent slice holes {holes[:3]}')
                if final and not cr['both_checkers']: problems.append(f't={t} {key}: unchecked closure')
            elif status != 'BUDGET':
                problems.append(f't={t} {key}: status {status}')
            counts[status] += 1
            cfgrecs.append(cr)
        totals[str(t)] = {'open_before':len(cfg),'closed_now':counts['CLOSED'],
                          'still_open':len(cfg)-counts['CLOSED'],
                          'checked_closed':sum(r['status']=='CLOSED' and r['slice_cover_ok'] and r['both_checkers'] for r in cfgrecs),
                          'status_counts':dict(counts)}
        configs_out[str(t)] = cfgrecs
    assert max_floor <= 600, max_floor
    # The finite exceptional lengths are covered by the pre-existing independent
    # lattice sweeps, which have been read (not silently rerun here).
    brute = {}
    for name in ('indep2/e_brute_600.json','indep3/i3_brute_600.json'):
        fn = os.path.join(ROOT,'verification',name)
        brute[name] = {'sha256':digest(fn),'members':json.load(open(fn))}
    audit = {'label':'COMPUTED','coverage':totals,'configurations':configs_out,
             'max_independent_slice_floor':max_floor,'finite_region_source':brute,
             'certificates':len(all_files),'both_checker_pass':sum(verified.values()),
             'problems':problems,'final':final}
    atomic_json(os.path.join(HERE,'coverage_summary.json'),audit)
    print(json.dumps({k:v for k,v in audit.items() if k not in ('configurations','finite_region_source')},indent=2))
    if final and problems: sys.exit(1)

if __name__ == '__main__': main()
