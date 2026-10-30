import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
copies=[];(L/'originals').mkdir(exist_ok=True)
index={p:(h,z) for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']}
for k in [130,153,82]:
 for name in ['SUMMARY.md','discovery.md']:
  p=L.parent/f'sol-fresh-source-discovery-r{k}'/name;b=p.read_bytes();rel=str(p.relative_to(R))
  assert index[rel]==(sha(b),len(b))
  dest=L/'originals'/f'r{k}-{name}';dest.write_bytes(b)
  copies.append(dict(original=rel,copy=str(dest.relative_to(L)),sha256=sha(b),bytes=len(b)))
save('original-copy-provenance.json',dict(utc=utc(),records=copies))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
save('guard-binding.json',dict(path=str(guard),sha256=sha(guard.read_bytes()),limits='Unchanged AS512MiB/group sampledRSS512MiB, CPU210/wall230; all helper/retrieval/extraction/hash commands guarded.'))
save('primary-hashes.json',dict(utc=utc(),records=[dict(path=str(p.relative_to(L)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted((L/'sources').iterdir()) if p.is_file()]))
save('search-receipt.json',dict(recorded_utc=utc(),method='public search tool, no browser',queries=[
 'arxiv "conjecture" "irreducibility" "2025" polynomials',
 'arxiv "conjecture" "log-concavity" "2026" polynomial coefficients',
 '"Irreducibility of truncations of the Catalan generating function"',
 'arxiv "conjecture" "polynomials" "divisibility" 2025 2024',
 '"Keith" "Nath" "Sellers" "114958"',
 '"On the discriminants of truncated logarithmic polynomials" proof conjecture',
 '"Irreducibility of truncations of the Catalan generating function" Seki journal'],
 selected_urls=['https://arxiv.org/abs/2609.10526','https://math.colgate.edu/~integers/z39/z39.pdf','https://arxiv.org/abs/2508.00074','https://experts.umn.edu/en/publications/on-simultaneous-ssts2t-core-partitions/'],limits='Search result descriptions are leads, not proof bodies. Primary retrieval UTC/hashes are in http.jsonl. Search queries not an exhaustive literature audit.'))
save('provenance.json',dict(utc=utc(),status='ZERO eligible fresh candidates',lane=str(L),counts_context=dict(additional=9,total=39,next=40),
 source_receipts='http.jsonl',primary_hashes='primary-hashes.json',qualified_history='history-receipt.json',history_screens=['early-screen.json','second-screen.json'],originals='original-copy-provenance.json',
 targets=[dict(title='On the discriminants of truncated logarithmic polynomials',authors=['John Cullinan','Rylan Gajek-Leonard'],doi='10.5281/zenodo.15283716',arxiv='2401.14138',statement='Conjecture1: all integer n>=1, Gal_Q(1+sum x^k/k)=S_n',decision='OLD INVESTIGATION; no decisive new universal route'),
 dict(title='Irreducibility of truncations of the Catalan generating function',authors=['Shin-ichiro Seki'],attribution='Zhi-Wei Sun, 2013',arxiv='2609.10526v1',statement='Theorem1.1: all n>=1, sum C_k x^k irreducible over Q',decision='EXCLUDE exact earlier public full-proof body'),
 dict(title='On simultaneous (s,s+t,s+2t,...)-core partitions',authors=['William J. Keith','Rishi Nath','James A. Sellers'],attribution='Fayers',arxiv='2508.00074v2',doi='10.1016/j.disc.2025.114958',statement='Conjecture1.14: all t>=2, s+t+(-1)^t divides f_t(s) in Z[s]',decision='EXCLUDE prior investigation and earlier public full residue proof')],
 registry_limits='No current registry HEAD clearance. Denied GitHub/public patch/diff routes not retried; inherited capped intervals/missing merge trees PARKED. No significant new mathematical investment or candidate nomination.',
 journal_limits='Actual logarithm journal body obtained. Seki latest observed preprint v1; journal not authenticated. Core latest observed preprint v2 obtained; institutional publication metadata is not journal body.',
 failures='failures.json',checks='checks.json',guard='guard-binding.json',novelty_claim=False,external_messages=False,children=False,shared_edits=False,lean_or_manuscript=False,
 freeze_policy='Scientific freeze covers all lane payload, including original copies and archived administrative snapshots, excluding only scientific-freeze.json (self), finalmanifest.json (later manifest), manifest-verification.json (later receipt). Final manifest includes scientific freeze, excludes only itself and verification receipt. Live NEXT/ledger are outside lane and not integrity targets.'))
def records(ex):
 return [dict(path=str(p.relative_to(L)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in ex]
ex=['scientific-freeze.json','finalmanifest.json','manifest-verification.json']
save('scientific-freeze.json',dict(utc=utc(),exclusions=ex,records=records(ex)))
ex=['finalmanifest.json','manifest-verification.json']
save('finalmanifest.json',dict(utc=utc(),exclusions=ex,records=records(ex)))
print('Frozen science and final manifest; run verify.py separately.')
