"""Write outputs/registry-screen.json from the lane's receipts and search logs."""
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
 'lane': 'expanded-corpus-r197',
 'candidate_screened': 350973,
 'lean_pool': {
   'head_endpoint': 'https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD',
   'head_sha': lp['sha'], 'head_commit_date': lp['commit']['committer']['date'], 'receipt': rec.get('lp-head'),
   'tree_and_projects_yml': 'HEAD equals root-recorded 01db1d70; reused byte-identical copies of expanded-corpus-r194/sources/leanpool-tree.json and leanpool-projects.yml (copied, re-hashed, hashes equal)',
   'leanpool_tree_sha256': h('sources/leanpool-tree.json'), 'leanpool_projects_yml_sha256': h('sources/leanpool-projects.yml'),
   'path_grep_terms': 'frieze quiddity banaian dissection dumont burstein checkerboard switching ryser chirotop dressian capparelli primc apn liebeck growable buratti multiplier coset bridge scaffold spiro ballot stirling (logs/leanpool-grep.log)',
   'projects_yml_grep_terms': '2106.06679 2002.12189 2212.07706 2001.05256 frieze banaian dumont burstein checkerboard ryser chirotop capparelli liebeck buratti scaffold spiro ballot stirling apn bridge-addable 381851 350973 345654 345190',
   'relevant_hits': 'none. LeanPool/FriezePatterns = "Maxima of Coxeter frieze patterns are Fibonacci numbers" (finite integral Conway-Coxeter friezes; unrelated to Banaian-Chen type Lambda / quotient dissections). APN project = Nagy-Vajda Kasami APN conjecture (unrelated to 345968). Other path hits are substring noise (Bridge, Scaffold, Stirling).'},
 'github_repository_search': {'queries_used': len(gh), 'limit': 8, 'spacing_seconds': 9, 'records': gh,
   'result': 'No 403/429. Only frieze-Lean hit: ElVec1o/vico_counting_friezes (counting positive rational friezes over (1/N)Z), unrelated. "switching checkerboards" hits are UI/game repos. All other queries total_count 0.'},
 'omega': {'head_sha': om['sha'], 'head_commit_date': om['commit']['committer']['date'], 'receipt_head': rec.get('omega-head'),
   'note': 'HEAD advanced beyond root-recorded f1c20718. Full recursive tree truncated (56638 entries); fetched D5 (a9124bf9..., 14037 entries, not truncated) and Problems (24a0aaeb..., 1752 entries, not truncated) subtrees recursively.',
   'receipts': {k: rec.get(k) for k in ('omega-tree', 'omega-root', 'omega-d5', 'omega-problems')},
   'grep_terms': 'frieze quiddity banaian dumont burstein switching 381851 350973 345654 345190 fragment bridgeaddable',
   'relevant_hits': 'none (D5 hits: SeidelSwitching, PrimeGaps Fragment* — unrelated; Problems: no hits)'},
 'openai_math': {'head_sha': oa['sha'], 'head_commit_date': oa['commit']['committer']['date'], 'receipt_head': rec.get('openai-head'),
   'note': 'HEAD unchanged from root-recorded 4eaee875; grepped cached complete preprint listing fresh-corpus-r10/sources/registry-preprints.json (sha256 6ac178a0...) for frieze|dumont|checkerboard|bridge-addable|banaian: no hits.'},
 'limits': 'Path/title screens only; no Lean file bodies read. J. Chen 2020 UMN REU slides not read.'
}
(L / 'outputs/registry-screen.json').write_text(json.dumps(out, indent=1) + '\n')
print('ok', out['lean_pool']['head_sha'], out['omega']['head_sha'], out['openai_math']['head_sha'])
