from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'lanes/parent-simon-threshold'
CANDIDATE = ROOT / 'candidates/simon-threshold'
REVIEW = ROOT / 'lanes/pi-simon-threshold-final-review'
assert not CANDIDATE.exists()
frozen = json.loads((SOURCE / 'review-hashes.json').read_text())
assert len(frozen) == 58
locations = dict((name, name) for name in frozen)
for name, digest in frozen.items():
    data = (SOURCE / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == digest, name
    out = CANDIDATE / name
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(data)
for name in ['main.tex', 'paper.pdf', 'paper-qa.json']:
    archive = 'reviews/final/reviewed/' + name
    out = CANDIDATE / archive
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes((SOURCE / name).read_bytes())
    locations[name] = archive
for name in ['review.md', 'provenance.json', 'frozen-before.json', 'page-1.png', 'page-2.png']:
    (CANDIDATE / 'reviews/final' / name).write_bytes((REVIEW / name).read_bytes())
for name, dest in [('audit.json', 'independent-audit.json'), ('Checks.log', 'independent-Checks.log')]:
    (CANDIDATE / 'verification' / dest).write_bytes(
        (REVIEW / 'replay/candidate-frozen/build/verified' / name).read_bytes())
assert (CANDIDATE / 'verification/parent-audit.json').read_bytes() == (
    CANDIDATE / 'verification/independent-audit.json').read_bytes()
for name in ['349140-acceptance-live.json', '349140-acceptance-receipt.json']:
    (CANDIDATE / 'sources' / name).write_bytes((SOURCE / 'sources' / name).read_bytes())
for name, value in [('reviewed-parent-hashes.json', frozen), ('reviewed-file-locations.json', locations)]:
    (CANDIDATE / name).write_text(json.dumps(value, indent=2) + '\n')
text = (CANDIDATE / 'main.tex').read_text()
text = text.replace(' Independent novelty and eligibility review is pending.', '')
text = text.replace('This is a proposed resolution', 'This is a resolution')
text = text.replace("The draft receives discovery credit zero pending independent source, mathematics, novelty and substantive-eligibility review, final manuscript checks and an extracted proof-packet replay. A short proof is not itself evidence of priority or eligibility under the campaign's counting standard.", 'The accompanying proof files include independent review and reproducible verification instructions.')
(CANDIDATE / 'main.tex').write_text(text)
(CANDIDATE / 'README.md').write_text('''# Simon threshold convexity

One combined resolution of the explicit threshold-convexity question in Simon,
arXiv:2012.11018v2, Section 3, page 5, final paragraph. For every gamma>1,
the literal infimum over admissible beta>0 is convex on (0,1/gamma).
The main MathDB 349140 complete-monotonicity equivalence is NOT resolved.

Read paper.pdf, formal/SourceConvex.lean, NOVELTY.md and reviews/final/review.md.
The independent review finds all five gates PASS and judges the result substantive
and eligible, while expressly recording its short, standard-tool-based character.
The new reduction is the exact literal-infimum/perspective-supremum identity.
Perspective convexity and supremum convexity are standard, credited ingredients.

All 58 reviewed original files are preserved, with reviewed-file-locations.json
mapping their original names to stored bytes. Release-paper edits remove only
operational draft-status prose; no mathematical claim or Lean source changes.
PROOF.md contains an additional informal strict-curvature route which is NOT
part of the formal result, release-paper theorem, or discovery credit.

Replay with pinned Lean 4.34.1 and the packages in verification/pins.json:
python3 verification/verify_candidate.py . --lean-bin /absolute/path/to/lean --packages /absolute/path/to/.lake/packages

The 26 declarations in 5 modules use only propext, Classical.choice, Quot.sound.
Parent and independent receipts are byte-identical. Extracted replay is required
before acceptance; acceptance.json and the campaign ledger record that final step.
Historical credit-zero/pending snapshots remain preserved as historical records.

No global priority claim. The publisher body and four closed citing bodies remain
unread; the bounded prior-art coverage and exact limits are documented.
''')
(CANDIDATE / 'proof-map.json').write_text(json.dumps({
    'literal_definitions': 'formal/ThresholdDefs.lean',
    'convex_kernel_and_perspective': 'formal/Perspective.lean',
    'rescaling_and_envelope': 'formal/Envelope.lean',
    'feasibility_and_positive_supremum': 'formal/Bounds.lean',
    'literal_infimum_and_closed_endpoint': 'formal/SourceConvex.lean',
    'endpoint': 'SimonThreshold.source_threshold_convex',
    'not_claimed': ['Main MathDB 349140 complete-monotonicity iff', 'Informal strict-curvature route']
}, indent=2) + '\n')
(CANDIDATE / 'reviews/parent-final-addendum.md').write_text('''# Parent reconciliation before final extraction

The entire independent review and provenance were read. Source, mathematics,
formal replay, eligibility and manuscript pass. The review judges the exact
infimum-to-perspective-supremum reduction substantive despite its short proof.
One combined separate-source-question outcome is proposed, not a resolution of
the main MathDB 349140 CM-equivalence conjecture. No helper receives extra credit.

N1: the informal strict-curvature route remains excluded. N2/N3: the weaker
admissible bound and harmless envelope generality require no change. N4: a fresh
parent acceptance-time API fetch returned HTTP 200, status open, progress null,
and all seven activity arrays empty; the JSON and receipt are included. This
confirms the separate main record's state, not novelty. N5/N6 need no changes.

The review's phrase about five years is bounded-search reporting: the source
states the question eluded its author in 2021, but no claim is made that the
author continued trying for five years. Likewise, no subsuming theorem was found
in the checked corpus; the review is not proof that none exists worldwide.
The unread publisher body, four closed citing bodies and absent comprehensive
MathSciNet/zbMATH/Scopus coverage remain material disclosed limits.

Only operational pending-review/credit-zero prose is removed from the release
paper. Reviewed original tex/PDF/QA bytes are archived, and all formal sources,
verifier and mathematical paper text remain unchanged. Release visual inspection
and a fresh extracted replay are required separately before final acceptance.
''')
print('Assembled', CANDIDATE, 'from 58 verified original files')
