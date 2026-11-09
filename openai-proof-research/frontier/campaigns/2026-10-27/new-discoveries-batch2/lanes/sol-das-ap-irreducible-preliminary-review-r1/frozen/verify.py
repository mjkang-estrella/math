"""Final integrity tool for lane claude-wide-finite-algebraic-scout-r245.

Run only through the guard:  ./g.sh python3 -P verify.py build   (writes provenance.json, manifest.json)
                             ./g.sh python3 -P verify.py check   (separate pass; writes receipt.json)
The manifest excludes itself and receipt.json.  `check` re-hashes every manifest entry,
re-confirms primary/ == frozen/ for each retrieved source and that each recorded fetch hash
still matches, and re-runs the capped mathematical checks of Theorem 1 (n = 4..14) and the
n = 5 hand counterexample.  It does not re-run long searches.
"""
import sys, json, hashlib, pathlib, datetime

L = pathlib.Path(__file__).resolve().parent
EXCLUDE = {'manifest.json', 'receipt.json'}


def h(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def files():
    for p in sorted(L.rglob('*')):
        if p.is_file() and p.name not in EXCLUDE and '__pycache__' not in p.parts:
            yield p


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def fetch_rows():
    return [json.loads(x) for x in (L / 'http.jsonl').read_text().splitlines() if x.strip()]


if sys.argv[1] == 'build':
    rows = fetch_rows()
    ex = [json.loads(x) for x in (L / 'extractions.jsonl').read_text().splitlines() if x.strip()]
    prov = {
        'lane': L.name, 'built_utc': now(),
        'counts': {'additional': 9, 'total': 39, 'next_global': 40, 'credit_claimed': 0},
        'guard': {'path': '../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',
                  'sha256': h(L.parent / 'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),
                  'caps': 'RLIMIT_AS 512MiB, group RSS 512MiB, CPU 210s, wall 230s; unchanged',
                  'env': 'OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 (+LC_ALL=C, MALLOC_ARENA_MAX=1, threads=1 for HiGHS)'},
        'admin_snapshot': (L / 'administrative/admin-snapshot-sha256.txt').read_text().splitlines()[:6],
        'retrievals': [{k: r.get(k) for k in ('name', 'url', 'utc', 'status', 'final_url', 'sha256', 'bytes', 'error')} for r in rows],
        'extractions': ex,
        'web_searches': [
            {'utc_date': '2026-10-30', 'mode': 'standard', 'query': '"AP-irreducible" sign pattern algebraic positivity conjecture 2n-2',
             'finding': 'only source paper, 1806.09641, 2412.06379, repository pages; no refutation/proof'},
            {'utc_date': '2026-10-30', 'mode': 'standard', 'query': 'sign patterns allow algebraic positivity Das conjecture counterexample minimally irreducible',
             'finding': 'same; IIT Guwahati thesis landing page identified (body not read)'}],
        'denied_or_unattempted': ['ScienceDirect LAA 653 (2022) journal body: denied route, not attempted',
                                  'IIT Guwahati thesis TH-2471 19MB PDF: not fetched (bounded)',
                                  'No GitHub API/raw/codeload, Google, proxy or browser routes used'],
        'history_screens': sorted(p.name for p in (L / 'administrative').glob('history-*.json')),
        'deviations_log': 'administrative/deviations.log',
        'principal_claims': {
            'theorem1': 'For n>=4 explicit F_n minimally AP-irreducible zero-diagonal with 4n-10 nonzeros; refutes Das 2112.00442v3 Conj 5.1 for all n>=5 (proof discovery.md)',
            'prop2': 'f(n) <= 6n-6 (proof discovery.md)',
            'computed': 'f(4)=6 exhaustive; f(5)=10 MILP gap 0 (solver evidence); n=6 MILP bad_alloc',
            'candidateA': 'no counterexample to 2305.00279 Conj 1 for n<=9 (floating-point screen)',
            'candidateDBG': '28/28 exact small cases agree with 2302.07239v2 Conj 3.3'},
    }
    (L / 'provenance.json').write_text(json.dumps(prov, indent=1))
    man = {'built_utc': now(), 'excludes': sorted(EXCLUDE),
           'files': {str(p.relative_to(L)): h(p) for p in files()}}
    (L / 'manifest.json').write_text(json.dumps(man, indent=0))
    print('manifest entries', len(man['files']))
elif sys.argv[1] == 'check':
    sys.path.insert(0, str(L / 'diagnostics'))
    from apirr import ap_irr, minimal
    from apfamily import family
    man = json.loads((L / 'manifest.json').read_text())
    bad = [k for k, v in man['files'].items() if not (L / k).is_file() or h(L / k) != v]
    extra = [str(p.relative_to(L)) for p in files() if str(p.relative_to(L)) not in man['files']]
    src_bad = []
    for r in fetch_rows():
        if 'copy' in r:
            a, b = L / 'primary' / r['name'], L / r['copy']
            if not (a.is_file() and b.is_file() and h(a) == h(b) == r['sha256']):
                src_bad.append(r['name'])
    fam = []
    for n in range(4, 15):
        A = family(n)
        fam.append(ap_irr(n, A) and minimal(n, A) and len(A) == 4 * n - 10)
    rows5 = ['000+-', '-0+00', '0+00+', '+0000', '00-+0']   # first random hit, hand-checked
    A5 = {(i, j): (1 if c == '+' else -1) for i, r in enumerate(rows5) for j, c in enumerate(r) if c != '0'}
    hand = ap_irr(5, A5) and minimal(5, A5) and len(A5) == 9
    ok = not bad and not extra and not src_bad and all(fam) and hand
    rec = {'checked_utc': now(), 'manifest_entries': len(man['files']), 'hash_mismatch_or_missing': bad,
           'unlisted_files': extra, 'source_copy_mismatch': src_bad, 'family_n4_to_14_pass': all(fam),
           'n5_hand_counterexample_9_nonzeros_pass': hand, 'manifest_sha256': h(L / 'manifest.json'), 'PASS': ok}
    (L / 'receipt.json').write_text(json.dumps(rec, indent=1))
    print(json.dumps(rec))
    sys.exit(0 if ok else 1)
