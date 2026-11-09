"""Reconcile every E/E2 configuration; independently replay E/E2 slice covers.
Usage: audit_results.py [--final]
Final mode requires a checker PASS with the current certificate hash, for both
checkers, for every generated certificate including partial configurations.
"""
import sys
sys.dont_write_bytecode = True
import os, json, glob, collections, itertools, functools, hashlib, math
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, HERE)
from inventory import configurations, enum_module
from breadth import atomic_json

@functools.cache
def digest(fn):
    h = hashlib.sha256()
    with open(fn,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): h.update(b)
    return h.hexdigest()

@functools.cache
def exact_solutions(fn):
    out = []
    with open(fn) as f:
        m = json.loads(next(f))
        for line in f:
            nd = json.loads(line)
            if nd['k']=='l' and 'sz' in nd['x']:
                for pt in nd['x']['sol']:
                    X = 10**pt[0] + m['K'] + sum(c*10**q for c,q in zip(m['coefs'],pt[1:]))
                    if X%9==0: out.append((X//9,pt[0]))
    return out

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
    for t in (16,24,32,14112):
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
        counts = collections.Counter(); cfgrecs = []; members = set()
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
                # E's cover intentionally contains redundant refinements. A
                # refined piece can be covered by a certificate leaving some
                # of its fixed digits free; exact (K,free) equality is too strict.
                K0 = 9*S-1
                def decode_fixed(K):
                    delta = K-K0
                    if delta < 0 or delta % 9: return None
                    ds = str(delta//9)[::-1]
                    fixed = {p:9*int(d) for p,d in enumerate(ds) if d!='0'}
                    if any(p<3 or c==81 for p,c in fixed.items()): return None
                    return fixed
                groups = collections.defaultdict(list)
                for (Kc,fc), vals in lookup.items():
                    fix = decode_fixed(Kc)
                    if fix is None: continue
                    if collections.Counter(fix.values()) + collections.Counter(fc) != collections.Counter(far): continue
                    groups[(Kc,fc)].extend(vals)
                covers = []
                for (Kc,fc), vals in groups.items():
                    unordered = [(fn,m) for fn,m in vals if m.get('domain','ordered')=='unordered']
                    if unordered:
                        fn,m = min(unordered,key=lambda v:v[1]['qmin'])
                        covers.append((decode_fixed(Kc),m['qmin'],{fn}))
                    orders = []
                    for od in sorted(set(itertools.permutations(fc))):
                        matches = [(fn,m) for fn,m in vals if m.get('domain','ordered')=='ordered' and tuple(m['coefs'])==od]
                        if not matches: break
                        orders.append(min(matches,key=lambda v:v[1]['qmin']))
                    else:
                        covers.append((decode_fixed(Kc),max(m['qmin'] for fn,m in orders),{fn for fn,m in orders}))
                for K,free,qmin,fixed in need:
                    max_floor = max(max_floor,qmin)
                    ef = decode_fixed(K)
                    assert ef is not None
                    for cf,floor,files in covers:
                        if any(ef.get(p)!=c for p,c in cf.items()): continue
                        remaining = [p for p in ef if p not in cf]
                        if any(p<floor for p in remaining): continue
                        if free and qmin<floor: continue
                        if not free and max(qmin,max(ef,default=-1)+1)<floor: continue
                        used.update(files); break
                    else: holes.append([K,list(free),qmin,list(fixed)])
                cr.update(slice_cover_ok=not holes, both_checkers=all(verified[fn] for fn in used),
                          independent_slice_count=len(need), certificate_count=len(used),
                          holes=holes, files=sorted(os.path.relpath(fn,HERE) for fn in used))
                genuine = set()
                for fn in used:
                    for n,L in exact_solutions(fn):
                        ds = str(n)[::-1]
                        if len(ds)!=L or math.prod(int(d) for d in ds)!=t: continue
                        s0 = sum((int(d)-1)*10**p for p,d in enumerate(ds[:3]))
                        f0 = tuple(sorted(9*(int(d)-1) for d in ds[3:] if d!='1'))
                        if s0==S and f0==far: genuine.add(n)
                cr['certificate_members'] = sorted(genuine)
                members.update(genuine)
                if holes: problems.append(f't={t} {key}: independent slice holes {holes[:3]}')
                if final and not cr['both_checkers']: problems.append(f't={t} {key}: unchecked closure')
            elif status != 'BUDGET':
                problems.append(f't={t} {key}: status {status}')
            counts[status] += 1
            cfgrecs.append(cr)
        totals[str(t)] = {'open_before':len(cfg),'closed_now':counts['CLOSED'],
                          'still_open':len(cfg)-counts['CLOSED'],
                          'checked_closed':sum(r['status']=='CLOSED' and r['slice_cover_ok'] and r['both_checkers'] for r in cfgrecs),
                          'certificate_members':sorted(members),
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
