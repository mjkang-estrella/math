import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
h=lambda p: hashlib.sha256((L/p).read_bytes()).hexdigest()
lp_head=json.loads((L/'sources/registry/leanpool-head.json').read_text())
om_head=json.loads((L/'sources/registry/omega-head.json').read_text())
oa_head=json.loads((L/'sources/registry/openai-math-head.json').read_text())
gh=json.loads((L/'outputs/github-search.json').read_text())
D5=json.loads((L/'sources/registry/omega-D5.json').read_text()); PR=json.loads((L/'sources/registry/omega-Problems.json').read_text())
rec={
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'lane':'expanded-corpus-r163',
 'lean_pool':{'repo':'Vilin97/lean-pool','head_route':'https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD',
   'head_sha':lp_head['sha'],'head_date':lp_head['commit']['committer']['date'],'head_receipt_sha256':h('sources/registry/leanpool-head.json'),
   'files_at_head':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((L/'sources/registry/leanpool').iterdir())},
   'tree':'reused byte-identical r164 tree at the same unchanged HEAD (sources/registry/leanpool-tree-from-r164.json, 25038 entries, truncated=false)',
   'tree_sha256':h('sources/registry/leanpool-tree-from-r164.json'),
   'keyword_script':'scripts/kw.py','keyword_hits':'outputs/leanpool-keyword-hits.txt',
   'queries':'all 18 source arXiv IDs, all 20 MathDB IDs, and per-ID distinctive keywords (see scripts/kw.py KW table) over projects.yml, every candidates/ file and the full tree path list',
   'verdict':'0 ID hits; every keyword hit read and judged generic/unrelated (e.g. Karl Petersen ergodic theory, Chvatal correlation conjecture, permanent formula lower bounds, noncrossing-pairing Catalan, Witt designs M12/M22). No prior Lean proof or refutation of any reserved conjecture.'},
 'github_repository_search':{'route':'https://api.github.com/search/repositories (unauthenticated, 7 s spacing)','records':'outputs/github-search.json',
   'queries':[{'q':r['query'],'status':r.get('status'),'total_count':r.get('total_count'),'hits':[x['full_name'] for x in r.get('hits',[])]} for r in gh],
   'denial':'HTTP 403 on query "generalized petersen diameter"; route stopped and not retried (rule).',
   'verdict':'only generic hit ericwang2004/combinatorial-designs-formalization (basic design theory library; not this conjecture). Not run for remaining queries because of the 403.'},
 'omega':{'head_route':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','head_sha':om_head['sha'],'head_date':om_head['commit']['committer']['date'],
   'D5_tree':{'sha':'8d6292cb61fefff73d6130c782fc1d42a5777a4c','truncated':D5.get('truncated'),'paths':len(D5['tree']),'sha256':h('sources/registry/omega-D5.json')},
   'Problems_tree':{'sha':'030d3ae42e13d7913c74595600ef8660083a5d5c','truncated':PR.get('truncated'),'paths':len(PR['tree']),'sha256':h('sources/registry/omega-Problems.json')},
   'path_screen':'scripts/treegrep.py with keywords design, liu-ding, ga1, antimagic, tropical, circulant, petersen, schur, steiner, inversion, plex, transversal, consum, distinguish, dichromatic, kneser, unicellular, schnyder, permanent, facial, matroid, trace, galois',
   'relevant':'Problems/zhang-tian-2025-steiner-diameter-radius-trees.md (same source as 382445 but about the trees paper; 382445 is settled by Reiswig 2024 regardless); no design, Liu-Ding, circulant edge-transitivity, tropical identity, Schur-triple or antimagic-join entries for reserved statements',
   'limit':'path screen only (file bodies not read)'},
 'openai_math':{'head_route':'https://api.github.com/repos/openai/math/commits/HEAD','head_sha':oa_head['sha'],'head_date':oa_head['commit']['committer']['date'],
   'note':'HEAD unchanged from root-verified 4eaee875; reused cached complete preprint listing ../fresh-corpus-r10/sources/registry-preprints.json (sha256 6ac178a0...): no design/antimagic/petersen/steiner/inversion/transversal paths; circulant hits are the circulant Hadamard conjecture (unrelated)'},
 'literature_routes':{'arXiv_abs_pages':'18 source abs pages fetched (versions recorded in outputs/source-versions.txt)',
   'web_search':'standard/extended searches for 339445, 337060, 336565 (x3), 339233 (x2): no resolutions found; 382445 resolved via the source body citing Reiswig 2024',
   'denials':'GitHub search 403 (stopped)'}
}
(L/'outputs/registry-screen.json').write_text(json.dumps(rec,indent=1,ensure_ascii=False)+'\n')
print('ok')
