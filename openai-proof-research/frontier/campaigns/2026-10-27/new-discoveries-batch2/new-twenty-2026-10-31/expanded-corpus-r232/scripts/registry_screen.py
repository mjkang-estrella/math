"""Write outputs/registry-screen.json: Lean Pool projects.yml grep (HEAD sha pinned), GitHub search results,
registry HEADs, and the public fence-rowmotion repository receipt.  Usage: registry_screen.py LANE"""
import sys, json, pathlib, re, hashlib
D = pathlib.Path(sys.argv[1]).resolve(); S = D / 'sources'
res = json.loads((D / 'reservation.json').read_text())
ids = [str(i) for i in res['ids']]
arx = sorted({r['source_url'].rsplit('/', 1)[1] for r in res['rows']})
kw = ['rowmotion', 'fence', 'Elizalde', 'Sagan', 'mesic', 'homomes', 'flag-accurate', 'flag_accurate', 'FlagAccurate',
      'strongly chordal', 'StronglyChordal', 'Amit', 'Ashurst', 'word map', 'WordMap', 'Laplacian spread', 'algebraic connectivity',
      'Borwein', 'Ismail', 'Ballantine', 'Merca', 'regular partition', 'Adinkra', 'friends-and-strangers', 'FriendsAndStrangers',
      'clique graph', 'CliqueGraph', 'real zero', 'amalgamation', 'stress-linked', 'Picard', 'Gregory', 'Kekul', 'robust coloring',
      'cycle double cover', 'Archdeacon', 'Cartesian product of trees', 'factorial']
y = (S / 'leanpool-projects.yml').read_text(errors='replace')
lines = y.splitlines()
hits = {}
for k in ids + arx + kw:
    m = [l.strip()[:200] for l in lines if re.search(re.escape(k), l, re.I)]
    if m: hits[k] = {'count': len(m), 'examples': m[:4]}
gh = {}
for p in sorted(S.glob('gh-search-*.json')):
    if p.name.endswith('.receipt.json'): continue
    rp = p.with_name(p.name + '.receipt.json')
    o = json.loads(p.read_text()); r = json.loads(rp.read_text())
    gh[p.name] = {'url': r['url'], 'status': r.get('status'), 'utc': r['utc'], 'total_count': o.get('total_count'),
                  'items': [(it['full_name'], it.get('created_at'), (it.get('description') or '')[:160]) for it in o.get('items', [])[:10]]}
heads = {}
for f in ['leanpool-head.json', 'omega-head.json', 'openai-math-head.json', 'gh-fence-head.json']:
    o = json.loads((S / f).read_text()); r = json.loads((S / (f + '.receipt.json')).read_text())
    heads[f] = {'url': r['url'], 'utc': r['utc'], 'sha': o.get('sha'), 'date': o['commit']['committer']['date']}
fr = json.loads((S / 'gh-fence-repo.json').read_text())
out = {'leanpool': {'head_sha': heads['leanpool-head.json']['sha'], 'projects_yml_url': json.loads((S / 'leanpool-projects.yml.receipt.json').read_text())['url'],
                    'projects_yml_sha256': hashlib.sha256((S / 'leanpool-projects.yml').read_bytes()).hexdigest(),
                    'patterns': ids + arx + kw, 'hits': hits},
       'github_repository_search': gh, 'registry_heads': heads,
       'public_prior_refutation_353231': {'repo': fr['full_name'], 'created_at': fr['created_at'], 'pushed_at': fr['pushed_at'],
                                         'description': fr['description'], 'head': heads['gh-fence-head.json']},
       'note': 'Omega/OpenAI-math HEADs recorded; their complete trees were not refetched in this lane (the cached root trees '
               'in staller-parent-final-r1 and fresh-corpus-r10 predate the current Omega HEAD); no candidate was proposed, so no '
               'candidate-specific tree grep was required.'}
(D / 'outputs' / 'registry-screen.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('leanpool hits', {k: v['count'] for k, v in hits.items()})
for k, v in gh.items(): print(k, v['status'], v['total_count'], v['items'][:3])
print(heads)
