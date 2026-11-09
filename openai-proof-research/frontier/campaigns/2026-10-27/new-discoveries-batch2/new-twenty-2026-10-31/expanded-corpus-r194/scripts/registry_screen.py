import json, pathlib, hashlib
L=pathlib.Path(__file__).resolve().parents[1]
gh=json.loads((L/'outputs/github-search.json').read_text())
rec={r['id']:r for r in json.loads((L/'outputs/fetch-receipts.json').read_text())}
h=lambda p: hashlib.sha256((L/p).read_bytes()).hexdigest()
head=json.loads((L/'sources/lp-head.json').read_text())
out={
 "lane":"expanded-corpus-r194",
 "lean_pool":{
  "head_endpoint":"https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD",
  "head_sha":head['sha'],"head_commit_date":head['commit']['committer']['date'],
  "receipt":{k:rec['lp-head'].get(k) for k in ('url','status','sha256','bytes','file','utc')},
  "tree_and_projects_yml":"HEAD unchanged from root's recorded 01db1d70; reused byte-identical copies of expanded-corpus-r191/sources/leanpool-tree.json and leanpool-projects.yml (copied into sources/ and re-hashed)",
  "leanpool_tree_sha256":h('sources/leanpool-tree.json'),"leanpool_projects_yml_sha256":h('sources/leanpool-projects.yml'),
  "path_grep_terms":"harmonic randic radius narayana polyomino govindarajan higherdim plane_partition partition_triangle matroid ef1 fairdiv grothendieck kohnert vexillary discriminant lacasse brlek palindrom binomialedge weaklyclosed elekes oligomorph ramseyexp amplituhedr bcfw litvak gaussianmin sumproduct (logs/leanpool-grep.log)",
  "projects_yml_grep_terms":"1210.2543 1203.4419 2606.11494 2602.02448 randi 'harmonic index' govindarajan matroid ef1 'fair division' grothendieck kohnert vexillary",
  "relevant_hits":"none. Path hits are substring noise (Harmonic analysis/PDE files, radius lemmas in analysis projects, GrothendieckVanishing sheaf cohomology, HardSphereNBC graphic/NBC matroids). projects.yml hits: Grothendieck vanishing theorem and Tutte's path theorem for matroids, both unrelated."},
 "github_repository_search":{"queries_used":len(gh),"limit":8,"spacing_seconds":9,"records":gh,
  "result":"5 queries returned total_count 0; 'randic index radius conjecture' returned one repository, ZavbiA/Graffiti-conjecture-on-Randic-index-vs.-radius, a student project (README: 'Projekt pri predmetu Financni praktikum', no Lean, no claimed proof or counterexample; receipt gh-zavbia-readme). No 403/429."},
 "omega_and_openai_math":"not re-fetched: no candidate reached the investment/nomination stage (all 20 IDs are known, source-refuted or parked after bounded searches), so no registry clearance is claimed for any candidate."
}
(L/'outputs/registry-screen.json').write_text(json.dumps(out,indent=1)+'\n'); print('ok',out['lean_pool']['head_sha'])
