#!/usr/bin/env python3
"""Root registry screen (2026-11-23): for every counted row, search by arXiv id of the source
  - issues and pull requests of the-omega-institute/trureturing,
  - code of mxym/math and of openai/math.
Polite pacing; retries on rate limits; resumable (skips rows already in the output file).
Usage: python3 -I -B root_registry_screen.py   (run from this directory)"""
import json, subprocess, time, sys
from pathlib import Path
D = Path(__file__).resolve().parent
ids = json.loads((D / 'arxiv-ids.json').read_text())
outp = D / 'root-registry-screen.json'
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
    if mid in res and not any(isinstance(v, dict) and 'error' in v for v in res[mid].values() if not isinstance(v, str)): continue
    if not ax: res[mid] = {'arxiv': None}; continue
    q = ax.split('v')[0] if ax[-2:-1] == 'v' else ax
    r = {'arxiv': q}
    r['omega_issues'] = gh(['search', 'issues', '--repo', 'the-omega-institute/trureturing', q, '--limit', '10', '--json', 'number,title,createdAt'], 2.5)
    r['omega_prs'] = gh(['search', 'prs', '--repo', 'the-omega-institute/trureturing', q, '--limit', '10', '--json', 'number,title,createdAt'], 2.5)
    r['mxym_code'] = gh(['search', 'code', '--repo', 'mxym/math', q, '--limit', '20', '--json', 'path'], 9)
    r['openai_math_code'] = gh(['search', 'code', '--repo', 'openai/math', q, '--limit', '20', '--json', 'path'], 9)
    res[mid] = r
    outp.write_text(json.dumps(res, indent=1))
    hits = {k: v for k, v in r.items() if k != 'arxiv' and v}
    print(mid, q, 'HITS ' + json.dumps(hits)[:400] if hits else 'clean', flush=True)
print('done', len(res))
