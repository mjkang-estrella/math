import json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
gh=json.loads((L/'outputs/github-search.json').read_text())
rec={r['id']:r for r in json.loads((L/'outputs/fetch-receipts.json').read_text())}
out={
 "utc_screen":"2026-11-05T03:30Z-03:33Z",
 "lean_pool":{
  "head_endpoint":"https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD",
  "head_sha":"01db1d7049cf9668bda1e9e106875ee1278b43e6","head_date":"2026-10-07T07:41:01Z",
  "receipt":{k:rec['lp-head'][k] for k in ('id','url','status','sha256','bytes','file','utc')},
  "tree_and_projects_yml":"HEAD unchanged from root's recorded sha; reused byte-identical copies of expanded-corpus-r185 sources/leanpool-tree.json (sha256 4bcaacb4aca9301527bafc9e6f916a38af7a7281d854b17384c454cb3cbd16a2, 25038 entries, truncated=False) and leanpool-projects.yml (sha256 70c00946a17e338df98e2975367fd69380a69e54e9197af31ffdc157d1013236), copied into sources/ and re-hashed",
  "grep_terms_paths":"domination exponential cyclicperm gridclass necklace signature obstacle bipyramid grothendieck skewshape overpartition crank tope hypercellular partialcube rationalcone listcolo choosab paintab polar additivebas semiprimitive design ternary permanent phi4 doublepoisson milnor eigenvalue archer lauderdale henning rautenbach (logs/leanpool-grep.log)",
  "grep_terms_projects_yml":"all 18 source arXiv IDs plus archer lauderdale rautenbach henning gubeladze chepoi knauer obstacle grothendieck patrias xiong overpartition crump giudici semiprimitive dimca arthamonov zhu choosab necklace domination",
  "relevant_hits":"none. Path hits are substring noise (e.g. 'tope' in 'operator', 'polar' in DavisKahan/Polar, GrothendieckVanishing = sheaf cohomology, 'design' in AsymptoticTrianglePacking, BeyondBethe/Permanent). projects.yml hits: grothendieck-vanishing, the names 'Henning Basold' and 'Zeru Zhu', and a 'domination' word in unrelated summaries."},
 "github_repository_search":{"queries_used":len(gh),"limit":8,"records":gh,
  "result":"all 6 queries returned total_count 0; no 403/429"},
 "omega_and_openai_math":"not re-fetched in this lane: no candidate survived to the investment stage (all 20 IDs are known, source-defective, source-resolved, routine bridges or parked open problems), so no registry clearance is claimed for any candidate."
}
(L/'outputs/registry-screen.json').write_text(json.dumps(out,indent=1)+'\n'); print('ok')
