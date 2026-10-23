#!/usr/bin/env python3
"""Prepare one isolated covering-density discovery brief; never dispatches."""
from pathlib import Path
import hashlib
import json
import re

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
D = Path(__file__).resolve().parent
old_raw = (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162z-brief.txt').read_bytes()
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old_raw.split(marker, 1)[1]
assert len(standing) == 5570
old = old_raw.decode()
prefix = old[:old.index('Catalogue access, if needed:')]
prefix = prefix.replace('r162z', 'r162aa').replace('Source090', 'Source092').replace('planar-energy operative-proof discovery', 'covering-density operative-proof discovery').replace('FOUR confirmed companions', 'TWO confirmed companions')
isolation = old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
previous = '''Arithmetic162z is CLOSED PREFREEZE/no nominee, with no frozen theorem or gate. Preserve its FULL diagnostic: ONE numerical C such that |E_log^*(n)-[(1/2-log2)n^2-(n/2)log n+C_tri*n]|<=C sqrt(n)log(n+1) for EVERY integer n>=2,for the optimal ORDERED-pair Euclidean-chord logarithmic energy on the UNIT sphere,where C_tri=2log2+(1/2)log(2/3)+3log(sqrt(pi)/Gamma(1/3)) is the exact paid triangular coefficient. No favorable n,different coefficient,separation assumption or one-sided replacement. The exact SAME-configuration heat reduction,one global H^-1 square,uniform self error,exponential triangular tail,cardinality correction from O(sqrt(n))-gap subsequences,and the prefreeze source-compatible curved-calibration lower comparison are retained payments,NOT independently graded or narrower nominees. The unpaid upper condition is ONE configuration for EVERY n whose local heat residual PLUS its SAME global field square is <=C sqrt(n)log(n+1). Retain identical charges,background,interface fluxes,counterterms and total correction energy. Qualitative screening constants,a quantitative construction at a different linear coefficient,per-cell winners,independent row phases and discarded cross terms do not close it. Particular curved residual-field routes are sufficient,not necessary to every proof. Method limits are not counterexamples or exhaustion. Full source reading,incomplete transitive primary ancestry,two opaque helper/status search false admissions and late stronger lower payment remain disclosed. All earlier scopes/dispositions stay immutable.

'''
direct = ['discovery-arithmetic-r162z-parent/assessment.md',
          'fresh-arithmetic-discovery-r162z/FINAL.md',
          'fresh-arithmetic-discovery-r162z/packet/private/prefreeze-mathematics.md',
          'fresh-arithmetic-discovery-r162z/packet/private/primary-understanding.md',
          'fresh-arithmetic-discovery-r162z/packet/private/READING-LIMITS.md']
inputs = []
for name in direct:
    path = B / name
    raw = path.read_bytes()
    inputs.append({'path': str(path.relative_to(P)), 'bytes': len(raw),
                   'mode': path.stat().st_mode, 'sha256': hashlib.sha256(raw).hexdigest()})
nav = json.loads((D / 'private/canonical-navigation.json').read_text())
catalogue = '''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[153911,155355),EXACT Source092 body. Parent decoded only the first TWO numeric-bold title strings from ONE bounded14000-byte window starting152756,then selected ONLY092 body as a distinct family. Source091's body was NOT decoded or selected. No child title locator,extra family,catalogue screen,ancestor hunt or whole-catalogue opening/decoding. Two confirmed folders have27 blobs/34 complete-tree entries including roots. Actual wrappers are build/main.tex and build/paper.tex,not two guessed main.tex files. Parent source-body reading:NONE. Metadata is navigation,not a theorem/proof interface.

Read these FIVE exact COMPLETED originals as narrow direct exceptions relative to frontier/campaigns/2026-10-14/:
'''
catalogue += '\n'.join(direct) + '''
These exact exceptions never authorize their containing namespaces,links,other copied/source bundles,role/brief/status/activity aliases or other peer findings. Protected completed bodies AND named metadata remain PRIVATE/local under original rights;any copies stay inside your own root. No old r35,R041,weighted Brunn-Minkowski or another prior exact-body exception propagates. No broader old-scan rerun.

'''
family = '''Your ONE developed family is SOURCE092: OPTIMAL-ORDER CONVEX-BODY COVERING DENSITY,SINGLE-LATTICE UPPER BOUNDS AND UNRESTRICTED TRANSLATIVE LOWER BODIES. Both pinned manuscripts AND ALL operative source proofs are stipulated TRUE,including formerly conjectural conclusions. Validate exact applicability and fresh deductions,not upstream truth.

Confirmed canonical folders and ACTUAL wrappers:
'''
for entry in nav['families']:
    w = entry['wrapper']
    family += f"{entry['folder']}\n{w['path']}\nbytes {w['size']}; Git blob {w['sha']}.\n"
family += '''
Authenticate ALL27 canonical blobs using complete-tree size/Git blob/SHA256,including READMEs,compiled PDFs,figures and every local object. Read BOTH complete actual theorem/proof bodies,operative ancestors and real nested mathematical includes,required companions,strongest relevant ACTUAL primary proof mechanisms,and eligible ORIGINAL-history sections BEFORE extended deductions or author drafting. Follow actual includes rather than filename conventions; the lower-body paper's actual wrapper is build/paper.tex. Distinguish semantic proof reading from duplicate PDF/typography/ancillary authentication. All operative source results are stipulated true;do not rerun code to audit them. Recover clipped seams,record durable mathematical understanding and exact source labels,primary versions/URLs/read extents,access failures and unread ancestry. Mathematics must dominate proportionate evidence work.

The ENTIRE source upper theorem is PAID: EVERY full-dimensional compact convex body in R^n,n>=2,with NO symmetry or boundary-regularity assumption,has a covering by translates along ONE full-rank lattice with density <=C n log n for absolute C. A finite union of lattice cosets is not a stronger substitute for this actual single-lattice result. The ENTIRE lower theorem is PAID: in EVERY sufficiently large dimension there is a CENTRALLY SYMMETRIC convex body whose unrestricted translative covering density is >=c n log n,for absolute c>0,even without the lattice restriction. Thus the full worst-case Theta(n log n) order for both lattice and unrestricted coverings is paid,and a universal linear upper bound for all convex bodies is disproved by the stipulated input. Do not nominate that false upper claim,another restatement of optimal order,a smooth/symmetric specialization or mere periodization.

Read exact density conventions,dimension thresholds,constants and stronger proof operations before using the headline. Inspect the actual single-lattice mechanism and the lower construction's localization,caps,blocks,Poisson,target,encoding and periodization interfaces. Their quantitative uniformity,allowed random choices,finite-description/complexity statements and transfer to ALL coverings are paid wherever proved. Do not declare a stronger witness property absent from a theorem statement before using the full proof. Standard affine invariance,linear images,volume/determinant changes,homothetic rescaling,products,elementary lattice/coset manipulations and direct Rogers/source/duality compositions are paid when all compatibility hypotheses match. A formal change of parameter or existential-to-finite-grid restatement is not automatically substantial.

A distinct quantitative,relative,coherent-family,algorithmic,hypothesis-removal or structural operation is eligible only after a CLOSED identifiable nonroutine step remains beyond the strongest compatible source/primary payment. New constants from direct optimization or encoding already supplied by the source are technical. A difficult unproved conjecture is not a finding. Failed naive Poisson/net/lattice compositions do not show stronger known operations fail. Read ACTUAL strongest primary covering/lattice/random-polytope/periodization proofs when invoked,not abstracts or another agent's ledger.

Track arbitrary convex bodies versus symmetric/smooth/polytopal subclasses,all n versus a subsequence,translations versus rotations,one lattice versus finitely many cosets,periodic versus arbitrary locally finite centers,and average density versus pointwise overlap/multiplicity. Retain the SAME body,volume normalization,lattice determinant,admissible center family,boundary convention and failure event across limiting/discretization/periodization steps. Uniform lower bounds must cover EVERY admissible covering in the exact class,not just independently sampled centers or a convenient finite candidate net. An existence theorem does not silently supply an efficient oracle or bit algorithm;state rational/real input access,finite description,dimension dependence,randomness and success guarantees honestly if proposing an algorithmic result.

Do not replace a proposed FULL scope by bounded aspect ratio,easy facet descriptions,small dimension,restricted center sets,finite boxes with favorable boundary,a convenient lattice shape,a fixed random seed,an extra separation/net assumption or mere expected density. Covering-density control does not itself control maximum multiplicity,common lattices for unrelated bodies or coherent restrictions;such a claimed enhancement needs its entire compatibility proof. Conversely,if the actual source already pays it,credit that operation rather than calling it new. Preserve every old frozen/PREFREEZE diagnostic and closed disposition,including full spherical,graph-metric and projection-body scopes. On overlap read eligible ACTUAL original-history mechanisms under the prospective guards;exact exceptions never open linked protected namespaces.

After complete operative reading choose and develop ONE distinct fully specified full-scope operation with sustained CONCRETE mathematics beyond a first failed shortcut. Try the strongest integrated source/primary payment before naming a bridge unpaid. Keep actual bodies,lattices,common witnesses,parameters,probability/entropy/density budgets and all compatibility interfaces. Preserve paid derivations,failed attempts and precise residuals. Freeze a viable exact theorem BEFORE author-proof development,then close every quantifier/constant/interface. If nothing closes,honest PREFREEZE/no nominee with exact gaps;no weaker substitute,self-grade,count,exhaustive clearance,global impossibility or worldwide-priority claim.

Keep all source/primary/history/search/extract/render/copied bodies AND named metadata PRIVATE/local under original rights. Prospectively serialize EVERY literal wildcard/substring rule below before optional filename traversal/body selection beyond the narrow exceptions,retaining r/no-r,flat/compound/role aliases. At most ONE correctly pruned original-history traversal with no size/extension cutoff on eligible authored UTF8 after pruning;no projectwide rg-then-filter,broad untracked inventory or old scan rerun. Disclose false admissions,coarse omissions,versions/read extents,truncation recovery,late reads and incomplete transitive ancestry. Seal YOUR own fresh exact selection ONCE with detached FINAL/MANIFEST/outside REPORT anchors,a read-only explicit-anchor verifier and proportionate tiny COPIED own-text controls. No inherited manifest over fewer files. Artifact checks are not math gates. No nested agents,shared/git writes,public/browser actions or downstream formal/manuscript/release work. Parent alone commissions independent correctness and separate actual-primary substantial-contribution reviews of a viable full author proof.

'''
text = prefix + previous + catalogue + family + isolation + '\nFurther prospective literal twins:\n*arithmetic*162aa* *arithmetic*r162aa*\n\n' + marker.decode() + standing.decode()
assert set(re.findall(r'\*[^\s,;()]*\*', old)) <= set(re.findall(r'\*[^\s,;()]*\*', text))
assert text.encode().split(marker, 1)[1] == standing
brief = B / 'expanded-target-2026-10-17/fresh-arithmetic-r162aa-brief.txt'
assert not brief.exists() and not list((B / 'fresh-arithmetic-discovery-r162aa').iterdir())
brief.write_text(text)
(D / 'private/completed-direct-inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
record = {'brief': str(brief.relative_to(P)), 'bytes': len(text.encode()),
          'sha256': hashlib.sha256(text.encode()).hexdigest(), 'standing_bytes_preserved': 5570,
          'all_previous_literal_guards_retained': True, 'source': '092',
          'catalogue_extent': [153911,155355], 'source091_body_not_selected': True,
          'canonical_blobs': 27, 'canonical_entries_including_roots': 34,
          'completed_direct_inputs': 5, 'parent_source_body_read': False, 'publication': 'STOPPED'}
(D / 'brief-preparation.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
