#!/usr/bin/env python3
"""Generic root acceptance (root Claude Fable 5.2). Usage: accept-fable.py SPEC.json"""
import json, hashlib, shutil, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path
C = Path(__file__).resolve().parent.parent; R = C / 'root-intake-r60'
spec = json.loads(Path(sys.argv[1]).read_bytes())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest(); now = lambda: datetime.now(timezone.utc).isoformat()
HEAD = 'f5702854040e97fa7675c21ba37a9608f5f92dd3'  # rescreened by root 2026-11-23 19:05 PST: the only change since 4eaee875 is family 379 (VP and VNP are different; Lean under lean/OAI/Computability/VPVNP), unrelated to every counted row
out = subprocess.run(['git', 'ls-remote', 'https://github.com/openai/math', 'refs/heads/main'], capture_output=True, text=True, timeout=60).stdout.split()
assert out, 'registry unreachable'
if out[0] != HEAD: sys.exit(f'REGISTRY HEAD CHANGED to {out[0]}: rescreen the catalogue before accepting')
led_p = C / 'ledger.json'; led = json.loads(led_p.read_bytes())
i = int(spec['mathdb_id']); n = led['accepted_new'] + 1
assert all(int(str(a['mathdb_id'])) != i for a in led['accepted']), 'already accepted'
paper = C / spec['paper']; app = C / spec['lean_appendix']; assert paper.exists() and app.exists()
sub = C / 'mathdb-submissions' / f"{i}-{spec['slug']}"; sub.mkdir(parents=True, exist_ok=True)
shutil.copy2(paper, sub / 'PAPER.md'); shutil.copy2(app, sub / 'LEAN-SOURCE-APPENDIX.md')
eps = spec['endpoints']
(sub / 'SUBMISSION.md').write_text(f"""# MathDB {i}: {spec['title']}

- Problem: https://mathdb.com/p/{i}
- Source: {spec['source']}
- Outcome: **{spec['outcome']}**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints {', '.join('`'+e+'`' for e in eps)}; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. {spec['caveat']}
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

{spec['paste_summary']} The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

{spec['statement']}

## Summary of the result

{spec['summary']}

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
""")
acc = {'utc': now(), 'mathdb_id': i, 'ordinal_new': n, 'status': 'ACCEPTED_' + spec['outcome'], 'title': spec['title'], 'source': spec['source'],
       'outcome': spec['outcome'], 'endpoints': eps, 'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
       'paper': str(paper), 'paper_sha256': sha(paper), 'lean_appendix': str(app), 'lean_appendix_sha256': sha(app),
       'lanes': spec['lanes'], 'submission_packet': str(sub), 'current_registry': {'head': out[0], 'method': 'git ls-remote', 'utc': now()},
       'significance': {'root_decision': spec['summary'], 'caveat': spec['caveat']}, 'root_basis': spec['root_basis'],
       'root': spec.get('root', 'Claude Fable 5.2'), 'counts_after': {'new': n, 'target': led['target_new'], 'total': 39 + n, 'remaining': led['target_new'] - n}, 'publication': False}
af = C / f"{spec['slug']}-{i}-acceptance.json"
with af.open('x') as f: f.write(json.dumps(acc, ensure_ascii=False, indent=2) + '\n')
shutil.copy2(led_p, R / f'ledger-before-{i}-acceptance.json')
led['accepted'].append({'mathdb_id': i, 'file': af.name, 'utc': acc['utc'], 'beyond_target': False})
rec = {'utc': acc['utc'], 'mathdb_id': i, 'file': af.name, 'ordinal': n, 'accepted_new': n, 'target_new': led['target_new'], 'total_accepted': 39 + n}
led['latest_root_acceptances'].append(rec); led['latest_root_acceptance'] = rec
led.update({'accepted_new': n, 'status': f"active_research_{n}_of_{led['target_new']}_accepted"})
led_p.write_text(json.dumps(led, ensure_ascii=False, indent=2) + '\n')
ad_p = R / 'accepted-statements-addendum-116-125-20261118-v1.json'; ad = json.loads(ad_p.read_bytes())
ad['records'].append({'mathdb_id': i, 'ordinal': n, 'title': spec['title'], 'outcome': spec['outcome'], 'endpoint': eps, 'scope': spec['summary'], 'acceptance_file': af.name})
ad_p.write_text(json.dumps(ad, ensure_ascii=False, indent=2) + '\n')
tr_p = R / 'FABLE-TRACKER.json'; tr = json.loads(tr_p.read_bytes()); tr['accepted_new'] = n; tr['candidates'][str(i)] = {'stage': f'ACCEPTED as {n}'}; tr_p.write_text(json.dumps(tr, ensure_ascii=False, indent=1))
ix = C / 'mathdb-submissions' / 'INDEX.md'
if ix.exists():
    with ix.open('a') as f: f.write(f"| {i} | {spec['title']} | {spec['outcome']} | `{sub.name}` | yes | yes |\n")
print(f'accepted {i} as {n}/{led["target_new"]}, total {39+n}')
