#!/usr/bin/env python3
"""Second root screen (2026-11-23): code search of github.com/10m-u/open-problems-catalog by the arXiv id
of the source of every counted row (a public AI-proof catalogue first seen in the prior-art audit).
Resumable; polite pacing; retries on rate limits."""
import json, subprocess, time
from pathlib import Path
D = Path(__file__).resolve().parent
ids = json.loads((D / 'arxiv-ids.json').read_text())
outp = D / 'root-registry-screen2.json'
res = json.loads(outp.read_text()) if outp.exists() else {}
def gh(args, pause):
    for attempt in range(4):
        p = subprocess.run(['gh'] + args, capture_output=True, text=True)
        if p.returncode == 0:
            time.sleep(pause)
            try: return json.loads(p.stdout or '[]')
            except Exception: return {'unparsed': p.stdout[:300]}
        err = (p.stderr or '')[:300]
        if 'rate limit' in err.lower() or '403' in err or 'secondary' in err.lower():
            time.sleep(70); continue
        time.sleep(pause); return {'error': err}
    return {'error': 'rate limited after retries'}
for mid, ax in ids.items():
    if mid in res and not (isinstance(res[mid].get('catalog_code'), dict) and 'error' in res[mid]['catalog_code']): continue
    if not ax: res[mid] = {'arxiv': None}; continue
    r = {'arxiv': ax, 'catalog_code': gh(['search', 'code', '--repo', '10m-u/open-problems-catalog', ax, '--limit', '20', '--json', 'path'], 8)}
    res[mid] = r
    outp.write_text(json.dumps(res, indent=1))
    print(mid, ax, ('HITS ' + json.dumps(r['catalog_code'])[:500]) if r['catalog_code'] else 'clean', flush=True)
print('done', len(res))
