"""Write outputs/registry-screen.json from receipts and search logs (expanded-corpus-r202)."""
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
 'lane': 'expanded-corpus-r202',
 'candidates_screened': 'none surviving; screen run for all 20 reserved topics (most finite: 341837, 350949, 340504, 323795-323799, 333320)',
 'lean_pool': {
   'head_endpoint': 'https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD',
   'head_sha': lp['sha'], 'head_commit_date': lp['commit']['committer']['date'], 'receipt': rec.get('lp-head'),
   'tree_and_projects_yml': 'HEAD equals root-recorded 01db1d70; reused byte copies of expanded-corpus-r199/sources/leanpool-tree.json and leanpool-projects.yml (re-hashed below)',
   'leanpool_tree_sha256': h('sources/leanpool-tree.json'), 'leanpool_projects_yml_sha256': h('sources/leanpool-projects.yml'),
   'grep': 'scripts/registry_grep.py, full log logs/registry-grep.log (keywords and the 17 source arXiv IDs)',
   'relevant_hits': 'none. Hits are unrelated (eigenvalue analysis files, Exercise516ThueMorse in domain theory, SemicircleCheck/GenusNoncrossing = noncrossing pairings/Catalan).'},
 'omega': {'head_sha': om['sha'], 'head_commit_date': om['commit']['committer']['date'], 'receipt_head': rec.get('omega-head'),
   'note': 'HEAD advanced beyond root-recorded f1c20718 and r199. Root tree fetched non-recursively; D5 (41f1db48...) and Problems (289452b0...) subtrees both changed and were refetched recursively (not truncated).',
   'receipts': {k: rec.get(k) for k in ('omega-root', 'omega-problems', 'omega-d5')},
   'relevant_hits': 'none for the reserved records. Ulas-family hits (gawron-ulas-2022-factorial-sign-conjecture-4-4, miska-ulas, sobolewski-ulas) concern other papers; S3/Combinatorics/PopStack/PopStackCrossing.lean is pop-stack sorting, not Pop-Tsack torsing; S3/Combinatorics/Latin/AlternatingSignMargins.lean is Latin-square related; oeis-a326244 noncrossing-nonnesting graph recurrence is unrelated to 336450. Path-level screen only.'},
 'openai_math': {'head_sha': oa['sha'], 'head_commit_date': oa['commit']['committer']['date'], 'receipt_head': rec.get('openai-head'),
   'note': 'HEAD unchanged from root-recorded 4eaee875; HEAD commit file list (281 files) has no keyword hits; complete preprint listing not re-screened (no candidate).'},
 'github_repository_search': {'queries_used': len(gh), 'limit': 8, 'spacing_seconds': 9, 'records': gh,
   'result': 'No 403/429. One relevant hit: yuma-mizuno/KR-mod9-lean, a public Lean 4 formalization of the three mod 9 Kanade-Russell sum = product identities (README fetched: sources/gh-krmod9-readme.json; arXiv:2609.09653), which settles 340504 as public prior art. All other queries total_count 0.'},
 'denied_routes': [r for r in rec.values() if 'error' in r],
 'limits': 'Path/title screens only; no Lean file bodies read. ACM DL full text of Blanco-Skora ISSAC 2023 denied (403) and not retried; the arXiv v2 TeX (final version) was read instead.'
}
(L / 'outputs/registry-screen.json').write_text(json.dumps(out, indent=1) + '\n')
print('ok', out['lean_pool']['head_sha'], out['omega']['head_sha'], out['openai_math']['head_sha'], len(out['denied_routes']))
