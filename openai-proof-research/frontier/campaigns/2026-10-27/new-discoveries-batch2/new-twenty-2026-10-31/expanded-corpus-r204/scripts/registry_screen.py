"""Write outputs/registry-screen.json from fetch receipts and search logs (expanded-corpus-r204)."""
import json, pathlib, hashlib
L = pathlib.Path(__file__).resolve().parents[1]
h = lambda p: hashlib.sha256((L / p).read_bytes()).hexdigest()
rec = {}
for r in json.loads((L / 'outputs/fetch-receipts.json').read_text()):
    rec[r['id']] = {k: r.get(k) for k in ('url', 'status', 'sha256', 'bytes', 'file', 'utc', 'error') if r.get(k) is not None}
head = lambda k: json.loads((L / f'sources/{k}.json').read_text())
gh = json.loads((L / 'outputs/github-search.json').read_text())
lp, om, oa = head('lp-head'), head('omega-head'), head('openai-head')
out = {
 'lane': 'expanded-corpus-r204',
 'candidates_screened': ['350721 (Alexandersson-Kebede cycle-length positivity)', '360653/361128 (Gurvich-Naumova GM Nash equilibrium)',
                         '351888 (Petrusevski-Skrekovski S-edge three-colour)', 'plus topic keywords for all 20 reserved records'],
 'lean_pool': {
   'head_endpoint': 'https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD',
   'head_sha': lp['sha'], 'head_commit_date': lp['commit']['committer']['date'], 'receipt': rec.get('lp-head'),
   'tree_and_projects_yml': 'HEAD equals root-recorded 01db1d70; byte copies of expanded-corpus-r202/sources/leanpool-tree.json and leanpool-projects.yml reused (re-hashed here)',
   'leanpool_tree_sha256': h('sources/leanpool-tree.json'), 'leanpool_projects_yml_sha256': h('sources/leanpool-projects.yml'),
   'grep_logs': ['logs/registry-grep.log (broad topic keywords + 19 source arXiv IDs + 20 MathDB IDs)',
                 'logs/registry-focus-nim.log', 'logs/registry-focus-rlm-sedge.log'],
   'relevant_hits': 'none. Keyword hits are unrelated (Brouwer/Nash existence of mixed equilibria, Shannon entropy, MinimumDegreeMatching, OddSubdivisionDescent in Brill-Noether graphs).'},
 'omega': {'head_sha': om['sha'], 'head_commit_date': om['commit']['committer']['date'], 'receipt_head': rec.get('omega-head'),
   'note': 'HEAD advanced beyond root-recorded f1c20718 and r202-recorded 97f84965. Root tree fetched non-recursively; Problems subtree 289452b0 unchanged (r202 recursive copy reused); D5 (01ff6bac) and Reg (ce47f38a) refetched recursively, not truncated.',
   'receipts': {k: rec.get(k) for k in ('omega-root', 'omega-d5', 'omega-reg')},
   'omega_problems_sha256': h('sources/omega-problems.json'),
   'relevant_hits': 'none for the reserved records. Unrelated: gurvich-krnc-vyalyi amoeba confinement; divisor-NIM, Splythoff, CRIM, Abuku nimber-domination, Manabe amalgamation NIM certificates; derangement-ratio (Vatter) and derangement 2-adic files; caro-petrusevski-skrekovski-tuza grid problem; alexandersson-jal-quemener rook Eulerian interlacing. Path-level screen only (no file bodies read).'},
 'openai_math': {'head_sha': oa['sha'], 'head_commit_date': oa['commit']['committer']['date'], 'receipt_head': rec.get('openai-head'),
   'note': 'HEAD unchanged from root-recorded 4eaee875; HEAD commit file list (281 files) has no keyword hits; complete preprint listing not re-screened.'},
 'github_repository_search': {'queries_used': len(gh), 'limit': 8, 'spacing_seconds': 9, 'records': gh,
   'result': 'No 403/429. One hit with a matching author pair: JD-Jones-ASES/gn-lean (README fetched: sources/gh-gnlean-readme.json) formalizes the unrelated Gurvich-Naumova powers-of-three partition conjecture (arXiv:2508.00946), not the GM-rule Nash conjecture. All other hits unrelated (word-representable graph algorithm repos, non-mathematical repos) or total_count 0.'},
 'denied_routes': [r for r in rec.values() if 'error' in r],
 'limits': 'Path/title screens only; no Lean file bodies read. Unread versions of record: DAM 2024 (10.1016/j.dam.2024.07.018, for 361128) and JGT 104(3) 2023 (10.1002/jgt.22991, for 351888); a dlib.si URL returned an unrelated paper (receipt dlib-jgt-sedge).'
}
(L / 'outputs/registry-screen.json').write_text(json.dumps(out, indent=1) + '\n')
print('ok', out['lean_pool']['head_sha'], out['omega']['head_sha'], out['openai_math']['head_sha'], len(gh), len(out['denied_routes']))
