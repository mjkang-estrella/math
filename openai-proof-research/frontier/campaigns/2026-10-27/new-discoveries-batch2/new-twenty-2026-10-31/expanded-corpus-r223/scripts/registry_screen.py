"""Registry screen. usage: registry_screen.py LANE_DIR CACHE_DIR
Fetches Lean Pool HEAD (commits/HEAD), projects.yml at that sha; GitHub repository search (few spaced queries);
greps cached Omega D5/Problems path lists and the cached OpenAI preprints listing for keywords.
Writes outputs/registry-screen.json (never overwrites) and receipts in sources/registry/.
"""
import sys, json, hashlib, datetime, pathlib, time, urllib.request, urllib.parse
D = pathlib.Path(sys.argv[1]).resolve(); C = pathlib.Path(sys.argv[2]).resolve()
R = D / 'sources' / 'registry'; R.mkdir(exist_ok=True)
outp = D / 'outputs' / 'registry-screen.json'
if outp.exists():
    raise SystemExit('exists')
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
def get(name, url):
    rec = {'url': url, 'utc': now()}
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'Math-research-source-review/1.0', 'Accept': 'application/vnd.github+json'})
        with urllib.request.urlopen(req, timeout=25) as r:
            b = r.read(); rec.update(status=r.status, final_url=r.url, sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))
            (R / f'{name}.body').write_bytes(b)
    except Exception as e:
        b = None; rec.update(error=str(e), status=getattr(e, 'code', None))
    (R / f'{name}.receipt.json').write_text(json.dumps(rec, indent=1) + '\n')
    return rec, b
terms = ['2511.16611', 'Venturi', 'circular automat', 'irreducible automat', 'synchroniz', 'Cerny', 'Černý',
         '371607', '371606', '2511.17000', 'star edge', '371619', '2510.26664', 'Gowers', 'uncertainty',
         '2510.17337', 'Hadamard cube', '2511.03822', 'Hermite simplex', 'Smith normal', '2511.07248', 'private neighbor']
res = {'utc': now(), 'terms': terms}
rec, b = get('leanpool-head', 'https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD')
res['leanpool_head_receipt'] = rec
sha = json.loads(b)['sha'] if b else None
res['leanpool_head_sha'] = sha
if sha:
    rec2, b2 = get('leanpool-projects', f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/projects.yml')
    res['leanpool_projects_receipt'] = rec2
    t = b2.decode(errors='replace').lower() if b2 else ''
    res['leanpool_projects_hits'] = {k: t.count(k.lower()) for k in terms}
    rec3, b3 = get('leanpool-tree', f'https://api.github.com/repos/Vilin97/lean-pool/git/trees/{sha}?recursive=1')
    res['leanpool_tree_receipt'] = rec3
    if b3:
        paths = [x['path'] for x in json.loads(b3).get('tree', [])]
        res['leanpool_tree_paths'] = len(paths)
        res['leanpool_tree_truncated'] = json.loads(b3).get('truncated')
        res['leanpool_path_hits'] = {k: [p for p in paths if k.lower().replace(' ', '') in p.lower().replace('_', '').replace('-', '')][:20] for k in terms}
cache = {}
for f in ['omega-D5.paths', 'omega-Problems.paths', 'openai-head.body', 'leanpool-head.body', 'summary.json']:
    p = C / f
    if p.exists():
        t = p.read_text(errors='replace').lower()
        cache[f] = {'sha256': hashlib.sha256(p.read_bytes()).hexdigest(), 'hits': {k: t.count(k.lower()) for k in terms}}
res['cached_root_registry'] = {'dir': str(C), 'files': cache}
gh = []
for q in ['synchronizing automata lean irreducible', 'Cerny conjecture lean4 automata', 'circular automata irreducible rank']:
    time.sleep(7)
    rec, b = get('gh-search-' + str(len(gh)), 'https://api.github.com/search/repositories?q=' + urllib.parse.quote(q))
    item = {'query': q, 'receipt': rec}
    if b:
        j = json.loads(b); item['total_count'] = j.get('total_count'); item['repos'] = [x['full_name'] for x in j.get('items', [])[:15]]
    gh.append(item)
    if rec.get('status') in (403, 429):
        break
res['github_repo_search'] = gh
outp.write_text(json.dumps(res, indent=1) + '\n')
print(json.dumps({k: v for k, v in res.items() if k not in ('leanpool_head_receipt',)}, indent=1)[:6000])
