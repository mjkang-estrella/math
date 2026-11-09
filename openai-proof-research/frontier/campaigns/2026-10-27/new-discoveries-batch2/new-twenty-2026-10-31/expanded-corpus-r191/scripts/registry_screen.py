import json, pathlib, hashlib
L = pathlib.Path(__file__).resolve().parents[1]
gh = json.loads((L / 'outputs/github-search.json').read_text())
rec = {r['id']: r for r in json.loads((L / 'outputs/fetch-receipts.json').read_text())}
h = lambda p: hashlib.sha256((L / p).read_bytes()).hexdigest()
out = {
 "lane": "expanded-corpus-r191",
 "lean_pool": {
  "head_endpoint": "https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD",
  "head_sha": json.loads((L / 'sources/lp-head.json').read_text())['sha'],
  "head_commit_date": json.loads((L / 'sources/lp-head.json').read_text())['commit']['committer']['date'],
  "receipt": {k: rec['lp-head'].get(k) for k in ('url', 'status', 'sha256', 'bytes', 'file', 'utc')},
  "tree_and_projects_yml": "HEAD unchanged from root's recorded 01db1d70; reused byte-identical copies of expanded-corpus-r189/sources/leanpool-tree.json and leanpool-projects.yml (copied into sources/ and re-hashed)",
  "leanpool_tree_sha256": h('sources/leanpool-tree.json'), "leanpool_projects_yml_sha256": h('sources/leanpool-projects.yml'),
  "tree_entries": 25038, "tree_truncated": False,
  "path_grep_terms": "hamilton digraph dominat schenker rowmotion powergraph power_graph crucial fixab superabund opendomin shephard stackedpoly palindrom graphicalregular criticalideal corank khovanov franklrodl chainpartition gasarch weakkonig turan (logs/leanpool-grep-distinctive.log; a broader noisy first pass is in logs/leanpool-grep.log)",
  "projects_yml_grep_terms": "all 17 distinct source arXiv IDs of the 20 records (1401.1717 1401.3823 1401.6760 1402.0442 1402.3582 1402.6178 1403.2657 1504.06257 1505.04484 1505.04952 1506.07949 1507.05600 1508.04029 1509.07346 1509.07574 1510.02740 2103.14609) plus bang-jensen gutin cranston rabern kitaev grinberg roby doostabadi miska peterin xia alfaro tomon moreira rukavicka hamilton rowmotion crucial fixab 'power graph'",
  "relevant_hits": "none. Path hits are substring noise (DominatedConvergence/DominatedIntegral analysis files, CircuitComplexity/Digraph, IsoGraph/Canon/Dominate, Turan3 = Turan's theorem, Hamiltonian mechanics files, CorankOne in several complex variables). projects.yml hits: SardMoreira (Moreira's Sard theorem, unrelated), author names Xia/Moreira in unrelated projects, 'Hamiltonian' in physics summaries."},
 "github_repository_search": {"queries_used": len(gh), "limit": 8, "spacing_seconds": 9, "records": gh,
  "result": "all 8 queries returned total_count 0; no 403/429"},
 "omega_and_openai_math": "not re-fetched: no candidate survived to the investment stage (all 20 IDs are known, source-refuted, claimed-resolved or parked after bounded searches), so no registry clearance is claimed for any candidate."
}
(L / 'outputs/registry-screen.json').write_text(json.dumps(out, indent=1) + '\n'); print('ok', out['lean_pool']['head_sha'])
