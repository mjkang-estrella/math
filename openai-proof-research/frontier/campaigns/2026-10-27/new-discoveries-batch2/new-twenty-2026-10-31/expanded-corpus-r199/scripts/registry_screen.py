"""Write outputs/registry-screen.json from receipts and search logs (expanded-corpus-r199)."""
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
 'lane': 'expanded-corpus-r199',
 'candidates_screened': [337062, 381292],
 'lean_pool': {
   'head_endpoint': 'https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD',
   'head_sha': lp['sha'], 'head_commit_date': lp['commit']['committer']['date'], 'receipt': rec.get('lp-head'),
   'tree_and_projects_yml': 'HEAD equals root-recorded 01db1d70; reused byte-identical copies of expanded-corpus-r197/sources/leanpool-tree.json and leanpool-projects.yml (copied, re-hashed, hashes equal)',
   'leanpool_tree_sha256': h('sources/leanpool-tree.json'), 'leanpool_projects_yml_sha256': h('sources/leanpool-projects.yml'),
   'path_grep_terms': 'etweenness ircula ainbow haroni arayan ewmanMiranda DegreeSequence EdgeTransitive edgeTransitive owerfulSet oloop (logs/registry-grep-candidates.log); broad reserved-topic terms in logs/registry-grep.log',
   'projects_yml_grep_terms': 'betweenness circulant rainbow aharoni narayan 1709.04773 1605.06752 337062 381292 edge-transitive',
   'relevant_hits': 'none. LeanPool/AharoniKorman = Hollom disproof of the Aharoni-Korman poset conjecture (unrelated); Monsky/RainbowTriangles unrelated; "betweenness" in projects.yml only in Euclid-geometry axioms.'},
 'github_repository_search': {'queries_used': len(gh), 'limit': 8, 'spacing_seconds': 9, 'records': gh,
   'result': 'No 403/429. Only "edge betweenness uniform" returned hits (7 unrelated repositories: uniform-cost search, capacitor simulation, etc.). All other queries total_count 0.'},
 'omega': {'head_sha': om['sha'], 'head_commit_date': om['commit']['committer']['date'], 'receipt_head': rec.get('omega-head'),
   'note': 'HEAD advanced beyond root-recorded f1c20718 and r197 3978330. Root tree fetched non-recursively; D5 subtree changed (7284340e..., refetched recursively, 14040 entries, not truncated); Problems subtree unchanged (24a0aaeb..., r197 copy reused, 1752 entries).',
   'receipts': {k: rec.get(k) for k in ('omega-root', 'omega-d5')},
   'omega_problems_sha256': h('sources/omega-problems.json'),
   'relevant_hits': 'none for edge betweenness or the Aharoni-Howard degree conjecture. Circulant hits (ThreeQuarterCirculantConjecture, RoldanCirculantEnergy, LiTanCirculantPositivity, DaviesMariglianoCirculantOrbits, ...) concern other invariants; S3/Combinatorics/Graph/Rainbow/* (RankDescent, ReservoirConnector, RobustLayers, TwoEdgeChoices) has no Problems entry naming Aharoni-Howard or degree sequences (path-level screen only).'},
 'openai_math': {'head_sha': oa['sha'], 'head_commit_date': oa['commit']['committer']['date'], 'receipt_head': rec.get('openai-head'),
   'note': 'HEAD unchanged from root-recorded 4eaee875.'},
 'denied_routes': [r for r in rec.values() if 'error' in r],
 'limits': 'Path/title screens only; no Lean file bodies read. 2022 TAG follow-up (Coronicova Hurajova-Madaras-Narayan) PDF denied (403) at digitalcommons.georgiasouthern.edu and core.ac.uk; CPC 2017 Aharoni-Howard version of record not accessed (paywall).'
}
(L / 'outputs/registry-screen.json').write_text(json.dumps(out, indent=1) + '\n')
print('ok', out['lean_pool']['head_sha'], out['omega']['head_sha'], out['openai_math']['head_sha'], len(out['denied_routes']))
