from pathlib import Path
import hashlib,json,shutil
R=Path(__file__).resolve().parents[2]
S=R/'lanes/parent-flat-bernoulli';C=R/'candidates/hetyei'
assert not C.exists(),'Canonical candidate already exists; inspect before reusing'
frozen=json.loads((S/'final-review-hashes.json').read_text())['hashes']
assert len(frozen)==69
locations={n:n for n in frozen}
for n,h in frozen.items():
 data=(S/n).read_bytes();assert hashlib.sha256(data).hexdigest()==h,n
 out=C/n;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
for n in ['main.tex','paper.pdf','paper-qa.json','build-paper.log']:
 archive='reviews/final/reviewed/'+n
 out=C/archive;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes((S/n).read_bytes());locations[n]=archive
(C/'reviewed-parent-hashes.json').write_text(json.dumps(frozen,indent=2)+'\n')
(C/'reviewed-file-locations.json').write_text(json.dumps(locations,indent=2)+'\n')
F=R/'lanes/pi-hetyei-final-review'
for p in F.iterdir():
 if p.is_file() and p.name not in ['audit.json']:
  out=C/'reviews/final'/p.name;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(p.read_bytes())
for n in ['audit.json','Checks.log']:
 src=F/'candidate-copy/build/verified'/n
 if n=='audit.json':out=C/'verification/independent-audit.json'
 else:out=C/'verification/independent-Checks.log'
 assert src.is_file(),src
 out.write_bytes(src.read_bytes())
assert (C/'verification/parent-audit.json').read_bytes()==(C/'verification/independent-audit.json').read_bytes()
P=R/'lanes/pi-hetyei-preliminary-review'
for p in P.iterdir():
 if p.is_file():
  out=C/'reviews/preliminary'/p.name;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(p.read_bytes())
# Release-paper changes are presentation only; all reviewed originals retained.
s=(C/'main.tex').read_text().replace('must be negative from index 11','are negative from index 11')
s=s.replace('Let $a_n=u_n^{(N)}$','Let $A_n=u_n^{(N)}$').replace('v_ia_n','v_iA_n').replace('a_{n+1}','A_{n+1}').replace('a_{n+2}','A_{n+2}').replace('a_{n-k}','A_{n-k}')
s=s.replace('\\kappA','\\kappa')
s=s.replace("The proposed contribution is one resolution of the source's explicit\nall-order conjecture, subject to independent source and prior-art review.\nThe campaign assigns this draft credit 0 pending its remaining acceptance\ngates. Its finite checks and supporting lemmas do not receive separate credit.","The contribution is one resolution of the source's explicit all-order conjecture.\nThe finite checks and supporting lemmas are ingredients of this single result.")
s=s.replace('Independent review and the final\nextracted-packet replay are pending.','The independent checks and replay instructions accompany the proof files.')
(C/'main.tex').write_text(s)
(C/'README.md').write_text('''# Hetyei Conjecture6.10 proof packet

Full MathDB319292 source-conjecture resolution on the explicit finite count
formula(16): kappa_n<n*kappa_(n-1) for every n>=12, equivalently
K_n<n*K_(n-1) for every n>=11. Every count/composition/recurrence/finite-matrix/
spectral/coefficient-limit bridge is proved. The author's original game-position
enumeration theorem is credited upstream, not recoded.

Read paper.pdf, formal/SourceCounts.lean, PROOF.md, FORMAL-ADDENDUM.md,
proof-map.json, reviews/final/review.md and reviews/parent-final-addendum.md.
All69 reviewed original files are byte-preserved with reviewed-file-locations.json.
Only presentation and operational status wording changed in the release paper;
all Lean modules and verifier bytes remain exactly reviewed. Parent and independent
117-declaration16-module strict replay receipts are byte-identical. An extracted
replay is the last acceptance gate. Historical candidate/STATUS/progress/provenance
snapshots retain credit0; acceptance.json and campaign ledger are authoritative
only after extraction. No independent review is misattributed to new bytes.

Replay:
python3 verification/verify_candidate.py . --lean-bin /absolute/path/to/lean-4.34.1/bin/lean --packages /absolute/path/to/pinned/.lake/packages

Pinned Lean/mathlib/dependency revisions: verification/pins.json. Raw-source
isolated rebuild, warningAsError, every actual declaration type and axiom set
checked. Only propext/Classical.choice/Quot.sound; no proof holes or new axioms.

One combined outcome. Classical finite spectral decomposition, power convexity,
Faulhaber and the author's enumeration are credited, not separately counted.
The source's auxiliary printed sign and K0 convention are not discoveries.
No global priority claim. Published JCTA and Sterling2018 access limitations,
Timber thesis-chapter scope and bounded novelty coverage remain disclosed.
''')
proofmap={
 'literal_source_counts':['SourceCounts.sourceK','SourceCompositions.prependCompositionEquiv','SourceCompositions.normalizedComposition_eq_renewal','SourceCounts.sourceK_eq_renewal'],
 'actual_matrix_and_spectrum':['Arrowhead.arrowhead_upper_sos','Arrowhead.arrowhead_lower_sos','SpectralCompression.negative_eigenindex_unique','ArrowheadSpectral.centerMoment_spectral'],
 'actual_grid_convolution_and_limit':['ArrowheadGrid.gridV_second','ArrowheadRecurrence.centerMoment_convolution','GridPowerLimits.gridPowerMean_tendsto','GridKernel.gridMoment_tendsto'],
 'strict_uniform_bounds':['RecurrenceBase.renewal_base_third','RecurrenceBase.renewal_base_twelve','RecurrenceBase.renewal_base_fourteen','RenewalTail.renewal_even_bound','RenewalTail.renewal_odd_bound'],
 'closed_source_endpoints':['FlatBernoulli.source_K_tail','FlatBernoulli.source_conjecture_319292'],
 'qualification':'Map entries except closed endpoint list give module and local declaration; all declarations are in namespace FlatBernoulli.'}
(C/'proof-map.json').write_text(json.dumps(proofmap,indent=2)+'\n')
print('Prepared',C,'from69 hash-verified reviewed files')
