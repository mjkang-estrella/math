import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
h=lambda p: hashlib.sha256((L/p).read_bytes()).hexdigest()
lp=json.loads((L/'sources/registry/leanpool-head.json').read_text())
gh=json.loads((L/'outputs/github-search.json').read_text())
cr=json.loads((L/'sources/registry/combrig-head.json').read_text())
rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':'expanded-corpus-r167',
 'lean_pool':{'repo':'Vilin97/lean-pool','head_route':'https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD',
   'head_sha':lp['sha'],'head_date':lp['commit']['committer']['date'],'head_receipt_sha256':h('sources/registry/leanpool-head.json'),
   'files_at_head':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((L/'sources/registry/leanpool').iterdir())},
   'files_note':'HEAD fetched live 2026-11-04 and unchanged from root-cited 01db1d70 (2026-10-07); projects.yml and candidates/ files reused byte-identically from expanded-corpus-r165 (which reused r163 fetches at this sha); tree path list reused from r164.',
   'tree_sha256':h('sources/registry/leanpool-tree-from-r164.json'),
   'keyword_script':'scripts/kw.py','keyword_hits':'outputs/leanpool-keyword-hits.txt',
   'queries':'all 20 source arXiv IDs, all 20 MathDB IDs (hex-boundary regex), keywords egerv|deming|konig|pseudoline|bichromatic|rigidity|well-dominat|strong product|irredundant|colour-balanced|iswap|pieri|robinson-schensted|orlik|terao|zonotop|pancycl|bang-jensen|double wheel|induced minor|tree-independence|rainbow|kohnert|quadratic variet|rodl|ksba|connective|monochromatic component|apex',
   'verdict':'0 arXiv-ID or MathDB-ID hits. Keyword hits read: rigidity (Connes rigidity, Conway-Guy gap rigidity, lattice gauge plateau rigidity, BrillNoether banana rigidity files, bryangingechen/CombinatorialRigidity listing, pw/cn-rigidity-matroid point-group symmetric frameworks), Konig (Konig lemma libraries), Pieri (symmetric-function Pieri files), Rainbow (Monsky rainbow triangles), Robinson-Schensted (tomtreijn/rsk), apex (unrelated): none formalizes any reserved conjecture.'},
 'github_repository_search':{'route':'https://api.github.com/search/repositories (unauthenticated, 7 s spacing, 7 of the allowed 8 queries)','records':'outputs/github-search.json',
   'queries':[{'q':r['query'],'status':r.get('status'),'total_count':r.get('total_count'),'hits':[x['full_name'] for x in r.get('hits',[])]} for r in gh],
   'verdict':'all 7 queries HTTP 200; only hit pw/cn-rigidity-matroid (C_k-symmetric bar-joint frameworks; not abstract S_n-symmetric 2-rigidity matroids). No denial.'},
 'combinatorial_rigidity_dependency':{'repo':'https://github.com/bryangingechen/CombinatorialRigidity','head_route':'https://api.github.com/repos/bryangingechen/CombinatorialRigidity/commits/HEAD',
   'head_sha':cr['sha'],'head_date':cr['commit']['committer']['date'],
   'files':{p:h(p) for p in ['sources/registry/combrig-head.json','sources/registry/combrig-tree.json','sources/registry/combrig-CountMatroid.lean','sources/registry/combrig-Laman.lean','sources/registry/combrig-lakefile.toml','sources/registry/combrig-toolchain.txt']},
   'relevance':'Provides SimpleGraph.countMatroid V 2 3 (= R_n) via IndepMatroid.ofFinite; proposed dependency for the 373112 Lean endpoint. It does not contain Tyomkyn Conjecture 6.1 or symmetric abstract rigidity matroids (tree path list grepped). Toolchain v4.36.0-rc1 (differs from campaign pin). Not compiled here.'},
 'omega_and_openai_math':{'note':'Not re-fetched; brief records Omega HEAD f1c20718 and OpenAI/math HEAD 4eaee875 (2026-11-04). Path screen only: not cleared live by this lane; root should re-check before acceptance of 373112.'},
}
(L/'outputs/registry-screen.json').write_text(json.dumps(rec,indent=1,ensure_ascii=False)+'\n'); print('ok')
