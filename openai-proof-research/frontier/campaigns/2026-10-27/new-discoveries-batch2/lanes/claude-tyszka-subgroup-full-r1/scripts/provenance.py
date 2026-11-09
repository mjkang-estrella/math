"""Build provenance.json from lane logs. usage: provenance.py LANE_DIR"""
import sys, os, json
L = sys.argv[1]
rd = lambda p: open(os.path.join(L, p)).read()
def sha_lines(p):
    out = {}
    for line in rd(p).splitlines():
        h, f = line.split(None, 1); out[f.lstrip('*')] = h
    return out
http = [json.loads(x) for x in rd('work/http.jsonl').splitlines() if x.strip()]
P = {
 'lane': 'claude-tyszka-subgroup-full-r1',
 'start_utc': rd('work/start-utc.txt').strip(),
 'target': {'arxiv': 'math/0702558', 'version': 'v86 (4 Dec 2009 18:42:21 UTC), latest per live abs fetched 2026-10-30T07:57:15Z',
            'statement': 'Conjecture 3, printed p21', 'live_abs_sha256_equals_r214_frozen': True,
            'journal_note': 'abs Comments: shortened revised version in Math. Logic Quarterly 56 (2010) no.2 "Two conjectures on the arithmetic in R and C"; not obtained',
            'overlap': 'arXiv:0807.3010v25 (21 Nov 2008), frozen r214 copy read; Conjecture (I) and p10 integer remark'},
 'classical_bridge': {'citation': 'I. Borosh, M. Flahive, D. Rubin, B. Treybig, A sharp bound for solutions of linear Diophantine equations, Proc. Amer. Math. Soc. 105(4) (1989) 844-846',
                      'url': 'https://www.ams.org/journals/proc/1989-105-04/S0002-9939-1989-0955458-1/S0002-9939-1989-0955458-1.pdf',
                      'read': 'full 3-page body; Theorem p845 and proof p845-846', 'chronology': 'received 11 Dec 1987, revised 17 Aug 1988, published Apr 1989; predates all math/0702558 versions (2007-2009)'},
 'scientific_inputs_frozen_from': 'lanes/sol-fresh-source-discovery-r214',
 'scientific_originals_sha256': sha_lines('work/originals-before.sha256'),
 'scientific_copies_sha256': sha_lines('work/copies-before.sha256'),
 'scientific_after_check': 'originals and copies re-verified after work: all OK',
 'admin_snapshot_sha256_at_snapshot': sha_lines('admin-snapshot/originals.sha256'),
 'admin_after_check': 'live NEXT.md changed after snapshot (root-mutable); others unchanged; snapshot not a scientific input',
 'http': http,
 'downloads_sha256': sha_lines('work/dl-hashes.sha256'),
 'web_searches': ['standard: Borosh Flahive Rubin Treybig "A sharp bound for solutions of linear Diophantine equations" Proc. Amer. Math. Soc. 1989',
                  'standard: Tyszka "additive subgroup" "x_i+x_j=x_k" 2^(n-1) integer solution Borosh'],
 'guard': {'path': 'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',
           'sha256': '825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45', 'caps': 'AS/RSS 512MiB, CPU 210s, wall 230s; not raised'},
 'checker': {'script': 'scripts/checker.py', 'output': 'checks.json', 'stdout': 'work/checker.stdout', 'stderr': 'work/checker.stderr'},
 'counts': 'root alone accepts/counts/stages; 9 additional / 39 total, next 40 unchanged',
}
json.dump(P, open(os.path.join(L, 'provenance.json'), 'w'), indent=1)
print('ok', len(http), 'http records')
