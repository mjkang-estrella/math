"""Record read-only input integrity and this lane's review evidence."""
from pathlib import Path
import hashlib,json,datetime

lane=Path(__file__).resolve().parent
root=lane.parent/'root-hoggatt-r1'
campaign=lane.parent.parent
repo=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=root/'preliminary-review-hashes.json'
expected=json.loads(manifest.read_text())
checks=[dict(path=name,expected=want,actual=sha(root/name),ok=sha(root/name)==want) for name,want in expected.items()]
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
final=dict(time_utc=now,frozen_label='0aadc15c28 (user supplied; git not accessed)',manifest_sha256=sha(manifest),count=len(checks),all_match=all(x['ok'] for x in checks),files=checks)
(lane/'hash-verification-final.json').write_text(json.dumps(final,indent=2)+'\n')
cached_names=['hoggatt.txt','hoggatt.html','lamprecht.txt','lamprecht.html','leake-ryder.txt','q-convolution-2026.txt','dilks-thesis.pdf','mao-shi.txt','liu-mao.txt','chern-shi-logconvex.txt','cigler-proof.txt','registry-companion-2403.txt','narayana-symmetry.txt','formal-conjectures-hoggatt-issues.json','realrooted-hoggatt-issues.json']
inputs=[repo/'AGENTS.md',campaign/'AGENTS.md',campaign/'ledger.json',campaign/'prior-campaign-context.json',repo/'sources/upstream.json',repo/'sources/CONTENTS.md',repo/'sources/preprints-tree.json']
data=dict(
 review_lane=str(lane),reviewed_lane=str(root),created_utc=now,
 role='Independent solo preliminary review; not an acceptance/counting authority',
 gates=dict(SOURCE='Exact latest available arXiv target verified; full printed article not accessed',MATH='PASS written proof on correctly stated classical dependencies',NOVELTY='No earlier explicit endpoint located; bounded search only; exact classical mechanism subsumption proved',SUBSTANTIVE='NOT CLEARED: recommend exclusion as routine adaptation of FZZ induction under campaign rule',FORMAL='INCOMPLETE: three elementary helpers replayed, no full endpoint'),
 principal_finding='For p=1/Q, K_d=t*D_Q R_d(p)=[d]_p*t*R_(d-1)(p), so h *_p^d K_d=t*D_Q h. Lamprecht Thm30 applied with F=f,G=-g,H=K_d proves the full strict q-Markov lemma. GW4 applied to P(t),P(Qt) gives strict q-separation. These plus the known FZZ induction and Gaussian identity give the full candidate.',
 freeze_integrity=dict(initial='hash-verification-initial.json',final='hash-verification-final.json',all_64_match=final['all_match'],manifest_sha256=sha(manifest)),
 context_inputs=[dict(path=str(p),sha256=sha(p)) for p in inputs],
 primary_cached_sources=[dict(path=str(root/'sources'/n),sha256=sha(root/'sources'/n),access='read-only frozen source, independently inspected in this review') for n in cached_names],
 own_live_retrievals=json.loads((lane/'retrieval-manifest.json').read_text()),
 web_evidence=[str(p.relative_to(lane)) for p in sorted((lane/'sources').glob('web-*.json'))],
 publication_limits=[
  'FZZ journal article direct access HTTP403; indexed introduction and conclusion snippets inspected, full printed conjecture body not read.',
  'Original Garloff-Wagner PDF fetch timed out; actual original indexed Theorem4 body and FZZ complete restatement agree; full original proof unread.',
  'Lamprecht full theorem bodies read in arXiv1210.1102v1; published metadata verified, no separate full journal-body comparison.',
  'No exhaustive code, private registry, subscription citation index, all-language or unpublished-work search. MathDB empty solutions not used as novelty evidence.'
 ],
 public_queries=[
  '"Hadamard Products of Stable Polynomials Are Stable" theorem 4',
  '"Hoggatt" "Sturm" q conjecture proof',
  '"Analytic properties arising from the Baxter numbers"',
  '"Hoggatt" "q" "interlacing" proof 2026',
  '"Analytic properties arising from the Baxter numbers" "Conjecture"',
  '"q-Narayana" "real" roots',
  '"Hoggatt" "Lamprecht"',
  '"Hoggatt" "Sturm" -site:mathdb.com -site:oeis.org',
  '"Hoggatt" proof "q" site:github.com',
  '"Hoggatt" site:ideosphere.ai',
  '"2505.05873" proof conjecture -site:mathdb.com -site:oeis.org',
  'site:sciencedirect.com/science/article/abs/pii/S0022247X26002271 "Conclusion"',
  'site:sciencedirect.com/science/article/abs/pii/S0022247X26002271 "Conjecture 4.1"',
  '"Suffridge’s convolution theorem for polynomials" "2016"',
  '"q-Hoggatt" "interlacing"',
  '"Garloff_Wagner_Hadamard" "standard"',
  '"Analytic properties arising from the Baxter numbers" "To conclude"',
  '"Analytic properties arising from the Baxter numbers" "any positive integer"'
 ],
 checks=dict(lean=json.loads((lane/'bridge-replay.json').read_text()),finite_only=json.loads((lane/'independent_checks.json').read_text()),pdf_visual_pages='Dilks printed45-46, PDF53-54',mathlib_search='Read-only rg in Mathlib/Analysis, Mathlib/Combinatorics, Mathlib/Algebra/Polynomial; no matching GW/MacMahon/interlacing theorem located'),
 mutations='Only files inside assigned review lane; no git, ledger, shared index, source-lane modifications or public writes',
 manuscript_review='Not requested; no manuscript gate imposed',
 acceptance_or_count_change=False,
 initial_setup_note='First fetch script invocation failed before retrieval because bs4 absent; replaced extractor with standard-library HTMLParser. No installation or environment mutation.'
)
data['review_artifacts']=[dict(path=str(p.relative_to(lane)),sha256=sha(p)) for p in sorted(lane.rglob('*')) if p.is_file() and p.name!='provenance.json']
(lane/'provenance.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(dict(all_frozen_hashes_match=final['all_match'],checked=len(checks),artifacts=len(data['review_artifacts']),review=str(lane/'review.md')),indent=2))
assert final['all_match']
