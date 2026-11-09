import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
h=lambda p: hashlib.sha256((L/p).read_bytes()).hexdigest()
lp=json.loads((L/'sources/registry/leanpool-head.json').read_text())
gh=json.loads((L/'outputs/github-search.json').read_text())
rec={
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':'expanded-corpus-r165',
 'lean_pool':{'repo':'Vilin97/lean-pool','head_route':'https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD',
   'head_sha':lp['sha'],'head_date':lp['commit']['committer']['date'],'head_receipt_sha256':h('sources/registry/leanpool-head.json'),
   'files_at_head':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((L/'sources/registry/leanpool').iterdir())},
   'files_note':'HEAD unchanged from the root-cited 01db1d70 (2026-10-07); projects.yml and all candidates/ files reused byte-identically from expanded-corpus-r163/sources/registry/leanpool, which fetched them at this same sha; tree path list reused from r164 (sources/registry/leanpool-tree-from-r164.json).',
   'tree_sha256':h('sources/registry/leanpool-tree-from-r164.json'),
   'keyword_script':'scripts/kw.py','keyword_hits':'outputs/leanpool-keyword-hits.txt',
   'queries':'all 20 source arXiv IDs, all 20 MathDB IDs, and per-ID distinctive keywords (scripts/kw.py KW table) over projects.yml, every candidates/ file and the full tree path list',
   'verdict':'0 arXiv-ID or MathDB-ID hits. Keyword hits read: Reed-Solomon (zk/STIR crypto projects), guo (author handles), Mahler (Lehmer Mahler measure), Kneser (Kneser addition theorem), Hadwiger-Nelson bounds (lyfar/hadwiger-nelson-bounds-lean; unit-distance chi in [5,7], not epsilon-band graphs), Loomis (minimax), sequencing (Hoare rule): all unrelated. MATERIAL HIT for 331535: candidates_discovered.yml lists jarfo/cdc-statements ("cycle double cover theorem, proved from openai/cdc-lean"), JoseBrox/cycle-double-cover-formalization and Yuren-Tang/affine-cdc. Followed to openai/cdc-lean (see below).'},
 'openai_cdc_lean':{'repo':'https://github.com/openai/cdc-lean','created_at':'2026-06-24T03:34:37Z','pushed_at':'2026-07-09T20:20:10Z',
   'files':{'sources/registry/cdc-lean-repo.json':h('sources/registry/cdc-lean-repo.json'),'sources/registry/cdc-lean-README.md':h('sources/registry/cdc-lean-README.md'),'sources/registry/cdc-lean-Main.lean':h('sources/registry/cdc-lean-Main.lean')},
   'endpoint':'theorem CDCLean.cycleDoubleCover_of_bridgeless {V E} [Fintype V] [Fintype E] ... (G : FiniteGraph V E) (hb : G.Bridgeless) : Nonempty G.CycleDoubleCover',
   'read_depth':'README and Main.lean endpoint statement read; CycleDoubleCover definition file and proof bodies not read; not rebuilt (Claude lane may not run Lean).',
   'consequence':'331535 is a routine corollary (see results.json 331535).'},
 'github_repository_search':{'route':'https://api.github.com/search/repositories (unauthenticated, 7 s spacing, 6 of the allowed 8 queries)','records':'outputs/github-search.json',
   'queries':[{'q':r['query'],'status':r.get('status'),'total_count':r.get('total_count'),'hits':[x['full_name'] for x in r.get('hits',[])]} for r in gh],
   'verdict':'all six queries returned HTTP 200 with total_count 0. No denial encountered.'},
 'omega_and_openai_math':{'note':'Not re-fetched. No candidate survived to the investment stage, and the brief records Omega HEAD 6974dba0 and OpenAI/math HEAD 4eaee875 fetched 2026-11-04 by r163. The cached complete OpenAI preprint listing (../fresh-corpus-r10/sources/registry-preprints.json, sha256 6ac178a0...) was path-grepped for cycle/cdc/double-cover: only unrelated cycle-decomposition papers (e.g. A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026); no CDC preprint path. Path screen only.'},
}
(L/'outputs/registry-screen.json').write_text(json.dumps(rec,indent=1,ensure_ascii=False)+'\n'); print('ok')
