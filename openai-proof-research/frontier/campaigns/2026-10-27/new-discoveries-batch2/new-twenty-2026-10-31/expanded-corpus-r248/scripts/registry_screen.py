"""Registry screen for the 20 reserved IDs: Lean Pool (HEAD 01db1d70, cached projects.yml/candidates from
expanded-corpus-r215 at the same HEAD, sha256 recorded), Omega tree at current HEAD (fetched here), OpenAI/math
(HEAD unchanged 4eaee875; root's cached preprints listing). Case-insensitive literal key search.
Writes outputs/registry-screen.json (refuses overwrite)."""
import json, hashlib, os, glob
D = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248'
R215 = D.replace('expanded-corpus-r248', 'expanded-corpus-r215') + '/sources/'
PRE = D.replace('expanded-corpus-r248', 'fresh-corpus-r10') + '/sources/registry-preprints.json'
out = D + '/outputs/registry-screen.json'
if os.path.exists(out):
    raise SystemExit('exists')
ex = json.load(open(D + '/extracted.json'))
keys = sorted(set(list(ex.keys()) + [o['source_url'].rsplit('/', 1)[1] for o in ex.values()]))
words = ['in-out', 'haythorpe', 'glynn', 'moeini', 'rook', 'morales', 'loupekine', 'snark', 'facial unique', 'unique-maximum',
         'unique_maximum', 'abdian', 'multicone', 'niho', 'shuffle', 'zvonkine', 'fraenkel', 'beatty', 'colin', 'verdiere',
         'mubayi', 'optical', 'garver', 'associahedr', 'abelian complexity', 'kabelian', 'schnyder', 'reversal', 'harutyunyan',
         'separating hash', 'liu_ding', 'liuding', 'design code', 'cantor', 'currie', 'mcconville', 'lewis']
files = {}
for name in ['pool-LeanPool_projects.yml', 'pool-candidates_README.md', 'pool-candidates_discovered.yml', 'pool-candidates_decisions.jsonl',
             'pool-candidates_shortlist.md', 'pool-candidates_manual.txt', 'pool-candidates_provenance.jsonl', 'pool-candidates_provenance.md',
             'leanpool-tree.json']:
    p = R215 + name
    if os.path.exists(p):
        files['leanpool:' + name] = p
files['omega-tree@cae7cdbe'] = D + '/sources/omega-tree.body'
if os.path.exists(PRE):
    files['openai-preprints(root cache)'] = PRE
res = {'heads': {'leanpool': '01db1d7049cf9668bda1e9e106875ee1278b43e6 (fetched 2026-11-05, unchanged; r215 cache reused)',
                 'omega': 'cae7cdbecefe4e996733b5a31cf247b2c6292ac0 (fetched 2026-11-05)',
                 'openai': '4eaee87548250b2682affda7d05d947c05554bae (fetched 2026-11-05, unchanged; root preprints cache reused)'},
       'files': {}, 'hits': {}}
for label, p in files.items():
    b = open(p, 'rb').read()
    t = b.decode('utf-8', 'replace').lower()
    res['files'][label] = {'path': p, 'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)}
    for k in keys + words:
        kk = k.lower()
        c = t.count(kk)
        if c:
            pos = t.find(kk)
            snips = []
            while pos != -1 and len(snips) < 4:
                snips.append(t[max(0, pos - 80):pos + 80].replace('\n', ' '))
                pos = t.find(kk, pos + 1)
            res['hits'].setdefault(k, {})[label] = {'count': c, 'snippets': snips}
open(out, 'x').write(json.dumps(res, indent=1) + '\n')
for k, v in res['hits'].items():
    print(k, {l: x['count'] for l, x in v.items()})
print('files', list(res['files']))
