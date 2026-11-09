# r480 lane verifier. Usage: python3 -I verify.py LANE_DIR [--negative-test]
# Exit 0 only if every check passes (and, with --negative-test, every injected mutation is detected).
import json, hashlib, os, sys
LANE = os.path.abspath(sys.argv[1]); L = os.path.dirname(LANE)
CORP = os.path.join(L, 'pi-mathdb-full-corpus-inventory-r301'); INT = os.path.join(L, 'root-mathdb-breadth-intake-r479')
ANCHOR = {  # frozen before reading (work/intake-prefreeze.txt, runs/check_corpus.r1.txt)
    os.path.join(CORP, 'manifest.json'): ('4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15', 22047),
    os.path.join(INT, 'reserved-ids.json'): ('99bc0489b5cc1083b7be7107d1903fec12f8304a10391c7a9709b18075f4c37d', 1350),
    os.path.join(INT, 'manifest.json'): ('0d24dd3528a1cadfa0efdc6b95b59581d2fd396329ba46af401d67670208eb45', 40786),
}
EXCLUDE = {'manifest.json', 'final-receipt.json'}
FORBID = {372627, 372628, 368940, 404067, 364119}
def sha(p):
    h = hashlib.sha256(); n = 0
    with open(p, 'rb') as f:
        for c in iter(lambda: f.read(1 << 20), b''): h.update(c); n += len(c)
    return h.hexdigest(), n
def canon(r): return hashlib.sha256(json.dumps(r, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode('utf-8')).hexdigest()
def lane_files():
    out = set()
    for r, ds, fs in os.walk(LANE):
        for f in fs: out.add(os.path.relpath(os.path.join(r, f), LANE))
    return out
def run(state):
    errs = []
    D, B, M, P, RS, files, anchors = state['D'], state['B'], state['M'], state['P'], state['RS'], state['files'], state['anchors']
    shacache = state['sha']
    def S(p):
        if p not in shacache: shacache[p] = sha(p) if os.path.isfile(p) else None
        return shacache[p]
    for p, v in anchors.items():
        if S(p) != v: errs.append('anchor mismatch ' + p)
    # flat bindings (originals in place)
    for b in B['bindings']:
        if S(b['original']) != (b['sha256'], b['size']): errs.append('binding mismatch ' + b['original'])
    # corpus manifest: 20 chunks + 8 frozen inputs in place, and all bound
    cm = json.load(open(os.path.join(CORP, 'manifest.json')))
    bound = {b['original'] for b in B['bindings']}
    chunks = [f for f in cm['files'] if f['path'].startswith('corpus/')]
    if len(chunks) != 20: errs.append('chunk count %d' % len(chunks))
    if len(cm['frozen_inputs']) != 8: errs.append('frozen_inputs count %d' % len(cm['frozen_inputs']))
    for f in chunks + cm['frozen_inputs']:
        p = os.path.join(CORP, f['path'])
        if S(p) != (f['sha256'], f['bytes']): errs.append('corpus mismatch ' + f['path'])
        if p not in bound: errs.append('not bound ' + f['path'])
    # assignment / disjointness
    res = json.load(open(os.path.join(INT, 'reserved-ids.json')))
    ids = [d['mathdb_id'] for d in D]
    if ids != res['ids'] or len(ids) != 50 or len(set(ids)) != 50: errs.append('assignment mismatch')
    cov = set(json.load(open(os.path.join(INT, 'coverage-delta.json'))))
    if set(ids) & set(res['other_active_reservations']): errs.append('overlap other reservations')
    if set(ids) & FORBID: errs.append('forbidden id present')
    if {str(i) for i in ids} & cov: errs.append('overlap coverage-delta')
    # literal / canonical hashes against original chunk lines (in place)
    cache = {}
    for d in D:
        p = os.path.join(CORP, d['original_chunk'])
        if p not in cache: cache[p] = open(p, 'rb').read().split(b'\n')
        try: r = json.loads(cache[p][d['original_line'] - 1])
        except Exception: errs.append('bad line %s' % d['mathdb_id']); continue
        if r.get('mathdb_id') != d['mathdb_id']: errs.append('id/line mismatch %s' % d['mathdb_id'])
        if canon(r) != d['canonical_record_sha256']: errs.append('canonical mismatch %s' % d['mathdb_id'])
        if r.get('statement') != d['literal_statement']: errs.append('literal mismatch %s' % d['mathdb_id'])
        if hashlib.sha256(d['literal_statement'].encode('utf-8')).hexdigest() != d['statement_utf8_sha256']: errs.append('statement sha mismatch %s' % d['mathdb_id'])
        if d.get('accepted_credit') != 0: errs.append('credit nonzero %s' % d['mathdb_id'])
    if P.get('accepted_credit') != 0 or any(x.get('accepted_credit') != 0 for x in P['qualified_briefs'] + P['retained_not_qualified']): errs.append('proposal credit nonzero')
    if len(P['qualified_briefs']) > 3: errs.append('more than three qualified briefs')
    # retained sources
    for s in RS:
        for k in ('pdf', 'text'):
            if S(os.path.join(LANE, s[k + '_path'])) != (s[k + '_sha256'], s[k + '_bytes']): errs.append('source mismatch ' + s[k + '_path'])
    # exact manifest membership
    listed = {f['path'] for f in M['files']}
    if listed != files - EXCLUDE: errs.append('manifest membership: extra=%s missing=%s' % (sorted(files - EXCLUDE - listed)[:5], sorted(listed - (files - EXCLUDE))[:5]))
    if listed & EXCLUDE: errs.append('manifest lists excluded file')
    for f in M['files']:
        if S(os.path.join(LANE, f['path'])) != (f['sha256'], f['size']): errs.append('manifest hash mismatch ' + f['path'])
    return errs
def load():
    J = lambda f: json.load(open(os.path.join(LANE, f), encoding='utf-8'))
    return dict(D=J('dispositions.json'), B=J('bindings.json'), M=J('manifest.json'), P=J('proposals.json'), RS=J('retained-sources.json'),
                files=lane_files(), anchors=dict(ANCHOR), sha={})
base = load(); errs = run(base)
out = dict(lane=os.path.basename(LANE), checks_failed=len(errs), errors=errs[:20], dispositions=len(base['D']), manifest_files=len(base['M']['files']),
           flat_bindings=len(base['B']['bindings']), retained_sources=len(base['RS']))
if '--negative-test' in sys.argv:
    import copy
    neg = {}
    def mut(name, f):
        st = copy.deepcopy({k: v for k, v in base.items() if k != 'sha'}); st['sha'] = dict(base['sha']); f(st); neg[name] = len(run(st)) > 0
    mut('canonical_hash_flip', lambda s: s['D'][7].__setitem__('canonical_record_sha256', '0' * 64))
    mut('literal_edit', lambda s: s['D'][3].__setitem__('literal_statement', s['D'][3]['literal_statement'] + ' '))
    mut('drop_disposition', lambda s: s['D'].pop())
    mut('foreign_id', lambda s: s['D'][0].__setitem__('mathdb_id', 336019))
    mut('extra_lane_file', lambda s: s['files'].add('stray.log'))
    mut('chunk_anchor_flip', lambda s: s['anchors'].__setitem__(os.path.join(CORP, 'manifest.json'), ('f' * 64, 22047)))
    mut('binding_size_flip', lambda s: s['B']['bindings'][10].__setitem__('size', 1))
    mut('credit_nonzero', lambda s: s['D'][1].__setitem__('accepted_credit', 1))
    out['negative_tests'] = neg; out['negative_all_detected'] = all(neg.values())
print(json.dumps(out, indent=1))
sys.exit(0 if not errs and out.get('negative_all_detected', True) else 1)
