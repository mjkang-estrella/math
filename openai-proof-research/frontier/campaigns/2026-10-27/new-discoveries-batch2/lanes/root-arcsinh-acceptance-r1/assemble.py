#!/usr/bin/env python3
"""Assemble current-status release sources without changing reviewed mathematics."""
from pathlib import Path
import difflib, hashlib, json, re, shutil

base=Path(__file__).resolve().parent
batch=base.parents[1]
reviewed=batch/'lanes/root-arcsinh-complete-r1'
source=reviewed/'candidate'
target=batch/'candidates/arcsinh-positive'
assert not target.exists(), 'Do not overwrite a release candidate'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((reviewed/'final-review-hashes.json').read_text())
for name,h in freeze.items():assert sha(reviewed/name)==h,name
manifest=json.loads((source/'MANIFEST.json').read_text())
for name,h in manifest.items():assert sha(source/name)==h,name
target.mkdir(parents=True)
for name in manifest:
    dest=target/name;dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(source/name,dest)

historical=target/'historical';historical.mkdir()
for name in ('main.tex','paper.pdf','PROOF.md','SUMMARY.md','README.md',
             'provenance.json','PRIOR-ART-SCREEN.md','paper-qa.json'):
    shutil.copy2(target/name,historical/('reviewed-'+name))

old=(target/'main.tex').read_text()
new=old.replace(r'\author{Research draft; independent review pending}',
                r'\author{Research manuscript}')
new=new.replace("strict-concavity statement in \\cite[Conjecture~5.1]{YHWL}. Its strict\nTur\\'an consequence, for $p>2$ and $0<x<1$, follows from positivity and\nthe arithmetic--geometric mean inequality:",
"strict-concavity statement in \\cite[Conjecture~5.1]{YHWL}. Its strict\nTur\\'an consequence, for $p>2$ and $0<x<1$, follows from the strict\nmidpoint inequality in Theorem~\\ref{thm:main}, positivity and the\narithmetic--geometric mean inequality:")
start=new.index('This is a research draft. Independent source, mathematical, formal,')
end=new.index('\\begin{thebibliography}',start)
new=new[:start]+'''Independent source, mathematical, formal, manuscript and bounded
novelty reviews have been completed. The possible connection with a generic
reciprocal-norm parameter theorem was screened explicitly; no established
subsuming result was located within the recorded search limits. No
worldwide priority is claimed. The entire result is one family; supporting
identities and consequences are not separate outcomes.

'''+new[end:]

def math_blocks(s):
    patterns=[r'\$[^$]*\$',r'\\\[[\s\S]*?\\\]',
              r'\\begin\{equation\}[\s\S]*?\\end\{equation\}',
              r'\\begin\{theorem\}[\s\S]*?\\end\{theorem\}']
    return {p:re.findall(p,s) for p in patterns}
assert math_blocks(old)==math_blocks(new),'Mathematics changed'
(target/'main.tex').write_text(new)
(base/'manuscript-status-diff.patch').write_text(''.join(difflib.unified_diff(
 old.splitlines(True),new.splitlines(True),fromfile='reviewed/main.tex',tofile='release/main.tex')))

proof=(target/'PROOF.md').read_text();idx=proof.index('## Exact source target')
(target/'PROOF.md').write_text('''# Positive-parameter arcsinh concavity: complete ordinary proof

Independent preliminary and final source/math/formal/bounded novelty and
substantive reviews PASS; final manuscript and extracted-packet review PASS.
The original mathematical proof and all formal sources are unchanged.
Final root archive verification and acceptance are recorded separately.
The old small-p counterexample and all helpers remain uncredited.

'''+proof[idx:])

for kind,lane in [('preliminary','pi-arcsinh-positive-preliminary-review-r1'),
                  ('final','pi-arcsinh-positive-final-review-r1')]:
    root=batch/'lanes'/lane;dest=target/'reviews'/kind;dest.mkdir(parents=True)
    for name in ('review.md','provenance.json'):shutil.copy2(root/name,dest/name)
    if kind=='final':
        for name in ('math_check.py','math_check.out','generic_check.py','generic_check.out'):
            p=root/'own'/name
            if p.exists():shutil.copy2(p,dest/name)
        for name in ('audit.json','Checks.log'):
            shutil.copy2(root/'own/replay/verification'/name,dest/('replay-'+name))

(target/'reviews/ROOT-CORRECTIONS.md').write_text('''# Root corrections and adoption — 2026-10-28

The actual published Eq (1.14) is on printed page 834, PDF page 2.
Root personally re-read sources/survey-02.png. Earlier task, root note and
preliminary report page 835 references are erroneous. Conjecture 5.1 is
printed page 847. The mathematical statement, paper and formal endpoint
were unaffected. Original reports remain unaltered historical evidence.

The preliminary report's dimension-five counterexample only disproves
unrestricted reciprocal-norm concavity on all p>0. It does not exclude
the true elementary dimension-dependent range p>log(n)/2. The final
review explicitly confirmed this correction and searched the narrower
two-point/restricted-range literature and public formal registries. No
published same-object subsumer was found. No global-priority claim follows.

The final manuscript differs only in current review-status prose, a neutral
author label, and the explicit reference to the already-used strict midpoint
inequality for the Turan consequence. Every inline/displayed mathematical
block and theorem block is byte-identical; all formal sources are unchanged.
The root re-renders and visually checks the final PDF. These small prose
corrections are parent fixes; no new mathematical assertion was introduced.
''')

(target/'README.md').write_text('''# Generalized inverse hyperbolic sine: paper and Lean proof

For every real x>0, A(p,x)=integral_0^x (1+t^p)^(-1/p)dt is strictly
concave on p>log(2)/2. This resolves all of Yin–Huang–Wang–Lin (2019),
Conjecture 5.1 (p>1,0<x<1). No optimality or all-p>0 concavity is claimed.

paper.pdf and main.tex contain the complete ordinary argument. formal/
contains the genuine real-power/interval-integral certificate: 19 declarations
in five modules, standard three axioms only. Run python3 verify_candidate.py
to compile fresh sources, verify exact toolchain/package pins, and inspect
the generated actual types and axiom reports in verification/Checks.log.
No candidate oleans are bundled. The exact pinned installed Mathlib is a
dependency, not vendored here; another machine must configure its local paths.

reviews/ includes independent preliminary/final reports, the final reviewer's
fresh extracted replay receipt, and root corrections. Both reviews PASS with
bounded novelty and elementary-proof caveats. historical/ preserves the
reviewed manuscript and pre-review notes; those pending-status labels are
historical, superseded by this README and the current acceptance receipt.
The current final archive receipt and parent acceptance decision are saved
alongside this candidate in the campaign, bound to the archive SHA256.

One outcome only. The old excluded small-p witness, entropy identity,
derivatives, all-x extension and Turan consequence receive no separate credit.
No external posting or publication was performed by this assembly.
''')
(target/'SUMMARY.md').write_text('''# Scope and independent review

Complete exact 2019 Conjecture 5.1; stronger all-x>0,p>log(2)/2 theorem.
5 Lean modules /19 declarations; no residual premises; standard3 only.
Two independent reviews and independent extracted replay PASS. Current
paper review-status prose corrected after review without mathematical edits.
Root final deterministic archive verification and acceptance are separate
campaign receipts. Historical status notes remain in historical/. Bounded
novelty only; no worldwide priority or optimal-threshold claim.
''')
early=(target/'PRIOR-ART-SCREEN.md').read_text()
(target/'PRIOR-ART-SCREEN.md').write_text('''# Historical early prior-art screen

The following is the pre-review investigation, preserved as provenance.
Its pending labels and unread-body notes are superseded where explicitly
cleared by reviews/preliminary/review.md and reviews/final/review.md.
In particular RACSAM 2025 was later read and concerns a different problem.
No worldwide-priority guarantee is inferred from any negative search.

'''+early)

formal_names=[f'formal/{name}.lean' for name in
 ('SourceDefs','EntropyBound','KernelDerivative','KernelConcavity','SourceTheorem','Checks')]
for name in formal_names:assert sha(target/name)==sha(source/name),name
binding={'reviewed_freeze':'b4ef8ac1a09b89f07df3bacc2ff931aa7c36dc6b',
 'original_math_freeze':'dcef9ead57','reviewed_hash_entries_verified':len(freeze),
 'reviewed_archive_sha256':sha(reviewed/'packet/arcsinh-positive-paper-proof.zip'),
 'mathematical_latex_blocks_unchanged':True,
 'formal_sha256':{n:sha(target/n) for n in formal_names},
 'only_manuscript_changes':'status, neutral author label, explicit existing midpoint reference',
 'source_definition_page':834,'source_conjecture_page':847,'credit_pending_final_replay':0}
(base/'copy-bindings.json').write_text(json.dumps(binding,indent=2)+'\n')
(target/'provenance.json').write_text(json.dumps({
 'date':'2026-10-28','source':'Yin–Huang–Wang–Lin, JMI13(3)(2019)833–854, Conjecture5.1 p847',
 'definition':'Eq1.14 p834','source_pdf_sha256':sha(target/'sources/survey2019.pdf'),
 'source_url':'https://files.ele-math.com/articles/jmi-13-58.pdf',
 'formal_modules':5,'declarations':19,'allowed_axioms':['propext','Classical.choice','Quot.sound'],
 'review_status':'Independent preliminary and final PASS; final paper status prose updated by root only',
 'bounded_novelty':'No located prior resolution or established same-object subsumption; see both reviews for access limits',
 'historical_provenance':'historical/reviewed-provenance.json',
 'binding':binding},indent=2)+'\n')
print(target)
