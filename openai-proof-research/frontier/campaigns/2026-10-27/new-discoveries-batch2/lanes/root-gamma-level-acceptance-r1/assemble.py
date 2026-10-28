from pathlib import Path
import hashlib,json,shutil,re,difflib
base=Path(__file__).resolve().parent
batch=base.parents[1]
src=batch/'lanes/root-gamma-level-complete-r3'
dst=batch/'candidates/gamma-level-convexity'
assert not dst.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((src/'final-review-hashes.json').read_text())
for n,h in freeze.items():assert sha(src/n)==h,n
manifest=json.loads((src/'MANIFEST.json').read_text())
for n,h in manifest.items():
    assert sha(src/n)==h,n
    p=dst/n;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,p)
hist=dst/'historical';hist.mkdir()
for n in ['main.tex','paper.pdf','README.md','PROOF.md','provenance.json','paper-qa.json']:
    shutil.copy2(dst/n,hist/('reviewed-'+n))
old=(dst/'main.tex').read_text()
new=old.replace('The present manuscript is a draft of the complete ordinary proof.\nIts source statement, written proof and substantive eligibility have received\nindependent preliminary review, including reassessment of the explicit\nclassical-perspective reduction.', 'Independent source, mathematical, formal, manuscript and bounded novelty\nreviews are complete, including reassessment of the explicit\nclassical-perspective reduction.')
new=new.replace('Independent final review and discovery acceptance remain pending; the\ncandidate has zero discovery credit. Numerical checks are supplementary\nevidence only.', 'A separate independent final review reproduced the extracted replay and\ninspected every declaration type and axiom report. Numerical checks are\nsupplementary evidence only; the campaign acceptance record is separate.')
def maths(s):
    return [re.findall(p,s) for p in [r'\$[^$]*\$',r'\\\[[\s\S]*?\\\]',r'\\begin\{equation\}[\s\S]*?\\end\{equation\}',r'\\begin\{theorem\}[\s\S]*?\\end\{theorem\}']]
assert new!=old and maths(old)==maths(new)
(dst/'main.tex').write_text(new)
(base/'manuscript-status-diff.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='reviewed/main.tex',tofile='release/main.tex')))
p=(dst/'PROOF.md').read_text();p=p.replace('Complete mathematical proof and literal Lean certificate; independent final\nreview and acceptance pending. Candidate credit 0; batch accepted tally 1/30.', 'Complete mathematical proof and literal Lean certificate. Independent final\nreview and its fresh extracted replay PASS. The final root archive verification\nand acceptance are recorded separately; historical pending labels are preserved\nin historical/. All mathematical arguments and formal sources are unchanged.')
(dst/'PROOF.md').write_text(p)
r=batch/'lanes/pi-gamma-level-final-review-r1';rd=dst/'reviews/final';rd.mkdir(parents=True)
for n in ['review.md','provenance.json','ownchecks.py','ownchecks-result.json']:
    shutil.copy2(r/n,rd/n)
for n in ['audit.json','Checks.log']:
    shutil.copy2(r/'checks'/n,rd/('replay-'+n))
(dst/'reviews/ROOT-ADOPTION.md').write_text('''# Root adoption and limits — 2026-10-28

Root read the complete final review and completed thread. All gates PASS.
The proof uses classical perspective convexity: xF is exactly a shifted
perspective sum. The preliminary denial of this was wrong and is retained
only as historical evidence. Current proof and paper state it correctly.

The exclusion of routine corollaries is not restricted to published results
about the same object: a complete immediate classical reduction can also
exclude a candidate. Here root judges the exact Gamma normalization,
strictness across consecutive factors, and literal full-domain level-curve
assembly substantive enough to resolve the source's explicit question.
This is a boundary judgment, not evidence of a new general method. The
strongest contrary interpretation (a short classical perspective exercise)
is retained. No located established result already supplies the source
endpoint. Negative searches do not certify worldwide priority.

All-c>1 is one family; existence, uniqueness, classical convexity tools,
known x>=1 and helper lemmas earn no separate credits. The different
Mittag-Leffler complete-Bernstein questions are not resolved here. No exact
MathDB record for Remark16(a) is asserted. No external action was performed.

Post-review mathematical LaTeX blocks and all formal sources are unchanged.
Only the manuscript's review-status prose and package documentation changed.
Root re-renders every final page and replays a fresh final archive extraction.
''')
(dst/'README.md').write_text('''# Strict convexity of Gamma-ratio level curves

For every c>1 and x>0, a unique positive height h_c(x) satisfies
Gamma(h_c(x))Gamma(h_c(x)+2x)/Gamma(h_c(x)+x)^2=c.
The height is strictly convex on x>0. At c=2 this resolves published
Garrappa–Gerhold–Popolizio–Simon, JMAA551(2025)129588, Remark16(a).
The separate complete-Bernstein questions are not claimed.

paper.pdf and main.tex give the ordinary proof. Run python3 verify_candidate.py
for a fresh source replay: nine modules, 52 public declarations, standard
three axioms only, no residual premises. The verifier checks the absolute
Lean4.34.1 binary hash/version and all eight installed package revisions,
including Mathlib d13f23b723b. Dependency paths in pins/run_lean must be
configured on a different machine; no dependencies or candidate oleans
are vendored. Actual types and axiom reports are in verification/Checks.log.

reviews/ contains independent preliminary, perspective-reassessment and
final reports. All gates PASS within recorded bounded novelty limits.
ROOT-ADOPTION.md preserves the strongest short/routine objection and root's
judgment. Classical perspective convexity, Euler product and Jensen are
credited, not claimed new. historical/ preserves the exact reviewed paper
and status documents; their pending labels are superseded by this README.

One family only. The final archive receipt and acceptance decision are
separate campaign files bound to the precise archive SHA256. No posting,
publication, upload or MathDB edit has been performed.
''')
(dst/'SUMMARY.md').write_text('''# Completed scope and review

Full positive-domain strict convexity of genuine Gamma-ratio level heights,
all c>1 as one family. Published Remark16(a), c=2, resolved. Literal closed
Lean endpoint source_convexity and genuine existence/uniqueness, 9 modules,
52 declarations, standard three axioms only. Final independent extracted
replay PASS; current manuscript status prose corrected by root without
mathematical changes. Bounded novelty and short-proof caveat explicit.
Final deterministic archive replay and acceptance are separate receipts.
''')
for n in manifest:
    if n.startswith('formal/'):
        assert sha(src/n)==sha(dst/n),n
binding={'freeze':'c0bbeeddfcac228d7a840107ff0d6d787cc2f253','reviewed_hashes_verified':len(freeze),'formal_sources_unchanged':True,'mathematical_latex_blocks_unchanged':True,'reviewed_paper_sha256':sha(src/'paper.pdf'),'reviewed_archive_sha256':sha(src/'packet/gamma-level-convexity-paper-proof.zip'),'only_manuscript_change':'review-status prose','credit_before_final_acceptance':0}
(base/'copy-bindings.json').write_text(json.dumps(binding,indent=2)+'\n')
(dst/'provenance.json').write_text(json.dumps({'date':'2026-10-28','source':'GGPS, JMAA551(2025)129588, Lemma15/Remark16(a), actual VoR PDFpp12-13','source_url':'https://doi.org/10.1016/j.jmaa.2025.129588','source_pdf_sha256':sha(dst/'sources/jmaa-vor.pdf'),'review_status':'Independent preliminary, substantive-reassessment and final PASS; final paper status prose updated by root only','novelty_limit':'Bounded screen; no located prior resolution or subsuming Gamma-level theorem; no worldwide priority guarantee; short classical-mechanism objection retained','formal_modules':9,'formal_declarations':52,'historical_provenance':'historical/reviewed-provenance.json','binding':binding},indent=2)+'\n')
print(dst)
