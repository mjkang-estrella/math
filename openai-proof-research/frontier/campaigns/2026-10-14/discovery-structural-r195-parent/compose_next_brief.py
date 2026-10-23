#!/usr/bin/env python3
"""Prepare the distinct Source320 round with all prior prospective guards retained."""
import hashlib,json,datetime
from pathlib import Path
C=Path(__file__).resolve().parent.parent; P=C/'discovery-structural-r195-parent'; PROJECT=C.parents[2]
ET=C/'expanded-target-2026-10-17'; old=(ET/'fresh-structural-r195-brief.txt').read_text().split('\n')
header=old[:38]
header[0]='Structural discovery r196 — Source320: nonhomeomorphic closed aspherical four-manifolds with the same homotopy type; distinct operative-proof discovery.'
header[1]='Write ONLY frontier/campaigns/2026-10-14/fresh-structural-discovery-r196/.'
pos=header[9].index('The ORIGINAL INITIAL brief of Arithmetic162c')
header[9]=header[9][:pos]+(
    'The ORIGINAL INITIAL brief of Arithmetic162j continuation round1 (idx667, owned by the other parent thread; recorded running in the shared ledger) '
    'already contains the literal prospective guard *structural*r196* before this root or brief exists. Exclude the ENTIRE *arithmetic*r162* namespace, '
    '*owner-recovery*, and every peer body/parent/brief/copy/derivative/status/activity alias. Do not inspect, poll or steer that peer. '
    'Structural195 is now CLOSED whole-scope correctness PASS / contribution TECHNICAL, condition DISCHARGED, ZERO count. Exclude its entire author, '
    'both review and parent namespaces, including no-r aliases; no body exception is admitted. Do not rename, weaken or seek another grade on that target. '
    'Every previously listed live or completed namespace remains excluded. Install the no-r twin of EVERY wildcard and compare all literal guards and twins '
    'BEFORE any traversal, including *k369r134-* and *t185r144-*. Own structural196 namespace is excluded from broad authored-history scans; own files are usable. '
    'Exact admitted original-source/history paths do not admit containing directories. No peer result or status may be used as a premise. '
    'These are prospective prompt-level guards, not operating-system isolation.')
family='preprints/Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/'
with (PROJECT/'sources/CONTENTS.md').open('rb')as f:f.seek(545514);body=f.read(546475-545514)
assert body.startswith(b'**320. ') and b'**321.'not in body and b'lean/docs/'not in body
tree=json.loads((PROJECT/'sources/preprints-tree.json').read_text());entries=[x for x in tree['tree']if x['path'].startswith(family)]
assert len(entries)==16 and len([x for x in entries if x['type']=='blob'])==14
wrapper=next(x for x in entries if x['path']==family+'build/paper.tex')
assert wrapper['size']==2273 and wrapper['sha']=='c9373d9c4502fceb075831196b1ecaba80f39082'
target=[
    '',
    'Catalogue access for THIS round, if needed at all: ONLY direct binary seek/read sources/CONTENTS.md[545514,546475), exact Source320 body, SHA256 '+hashlib.sha256(body).hexdigest()+'. No catalogue traversal, new heading locator, whole catalogue read/decode or second family. The parent used one bounded 3000-byte navigation seek starting at545514 to locate the321 header; that window also displayed321/322 and the opening of323 as navigation only. Only320 is selected. No Lean documentation link appears in320. Parent has not read any source theorem/proof body for this round.',
    '',
    'Your ONE developed family is Source320, Nonhomeomorphic closed aspherical four-manifolds with the same homotopy type. The complete pinned tree has ONE canonical folder '+family+' with16 entries /14 blobs: README, build/paper.tex, build/references.tex, ten section files under build/sections, compiled paper.pdf. Confirmed wrapper '+family+'build/paper.tex,2273bytes,Git blobc9373d9c4502fceb075831196b1ecaba80f39082. Authenticate all14 blobs and establish actual operative input order and nested dependencies from the wrapper and bodies. Do not infer mathematical content from filenames. Read all actual theorem statements, all operative proofs and required companions before extended deduction or drafting.',
    '',
    'Source AND ALL operative upstream proof operations at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE. Per catalogue, the source constructs closed connected aspherical topological four-manifolds that are homotopy equivalent but not homeomorphic, with a common word-hyperbolic fundamental group, and supplies a self-homotopy equivalence of one example not homotopic to a homeomorphism. These headlines and their actual construction/detection/transport operations are PAID. Validate new applicability and deductions, not upstream truth or conflict with Borel expectations. Establish from the bodies exactly which categories, orientations, markings, dimensions, group hypotheses and equivalence notions are present.',
    '',
    'Develop a DISTINCT substantial full-scope consequence or extension after the strongest compatible source/classical/primary reduction. Do not decide a theorem from the catalogue alone. First identify what the source proof already makes routine. Merely multiplying examples, reindexing a family, applying a standard product/cover operation, restating a structure-set obstruction or upgrading a headline by an already-paid source parameter is not automatically substantial. Conversely do not declare a transfer unpaid before trying the strongest compatible construction concretely. Seek a closed nonroutine operation with all required map, marking, group-action and category compatibilities. Quantitative results or genuine hypothesis removal are eligible only if the residual operation is identified and proved. Scope must remain exact and immutable once frozen.',
    '',
    'Relevant original-history navigation should use the ACTUAL construction and primitive aliases learned from the source, in addition to Borel, aspherical, topological four-manifold, homotopy equivalence, homeomorphism, word-hyperbolic group, structure set, surgery, normal invariant, rigidity and chamber/reflection terms only where the body uses them. Search eligible authored originals with every inherited prospective guard installed, follow operative sections through the next equal/higher heading, and distinguish semantic reading from lexical/heading navigation. Consult actual strongest primary proofs and source companions, not abstracts or other agents summaries. Disclose inaccessible originals and extraction/read limits; those are not evidence of novelty. Keep protected bodies and named metadata private/local under original rights.',
    '',
    'No completed-round body is directly admitted by this brief. Preserve ALL old frozen scopes and grades. Structural195 remains PASS/TECHNICAL zero-count on the exact countable independent fp-type-two family and its full consequences; no retry. Structural191 remains PREFREEZE/no nominee on finite-support filling columns with simultaneous power-decay residual and power-growth norm bounds for finite aspherical integral PD4 complexes; that quantitative filling target is not reopened or silently narrowed here. Structural194 chromatic splitting, Structural193 Gray-cylinder realization, Structural192 Steenrod/Dickson actions, and all arithmetic/analytic archives remain unchanged. On any relevant eligible historical overlap read the actual original scope before proposing a distinct theorem; an excluded root is not licensed merely by an overlap. Record the resulting limitation honestly.',
    '',
    'Perform sustained mathematical derivation, with durable notes. Before full proof development freeze only a viable exact theorem after prefreeze feasibility and source/primary/history comparison. Then prove the ENTIRE frozen statement, including every quantifier and compatibility, or preserve it and state the precise unresolved obligation. If no viable full result emerges, report PREFREEZE/no nominee with the actual derivations and gaps, not a substitute theorem or exhaustion claim. No self correctness/contribution/acceptance/count grades. Seal your OWN exact selected packet once with detached FINAL/MANIFEST/outside REPORT anchors, a read-only verifier and proportionate tiny copied controls. No nested agents, git/shared edits, publication, browser or downstream work.',
    '',
]
assert old[55].startswith('--- COMPLETE ORIGINAL STANDING BRIEF')
text='\n'.join(header+target+old[55:]);out=ET/'fresh-structural-r196-brief.txt';assert not out.exists();out.write_text(text)
metadata={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':str(out.relative_to(C)),
          'bytes':out.stat().st_size,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),
          'output':'fresh-structural-discovery-r196','catalogue_extent':[545514,546475],
          'catalogue_sha256':hashlib.sha256(body).hexdigest(),'canonical_folder':family,'canonical_blobs':14,'tree_entries':16,
          'wrapper':{k:wrapper[k]for k in ('path','sha','size')},'source_body_read_by_parent':False}
(P/'next-discovery-preparation.json').write_text(json.dumps(metadata,indent=2)+'\n')
print(json.dumps(metadata,indent=2))
